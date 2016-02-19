module Prover where

import Test.HUnit
import Test.QuickCheck
import Data.List (partition, (\\))
import qualified Data.Maybe (isJust)
import Control.Monad

import Prop

---- Proofs ----

type Env = [Prop]
data Proof = ImplI ProofProp
           | ImplE ProofProp ProofProp
           | ConjI ProofProp ProofProp
           | ConjE ProofProp
           | DisjIL ProofProp
           | DisjIR ProofProp
           | DisjE ProofProp ProofProp
           | Ass
           deriving Show
type ProofProp = (Proof, Env, Prop)

propOf  (_, _, prop)  = prop
envOf   (_, env, _)   = env
proofOf (proof, _, _) = proof

matchOne x [] = Nothing
matchOne x (y:ys) | x == y    = Just ys
             | otherwise = case matchOne x ys of
                             Nothing -> Nothing
                             Just ys' -> Just (y:ys')

match [] e2 = ([], [], e2)
match (x:xs) e2 =
  case matchOne x e2 of
    Nothing ->
      let (l, m, r) = match xs e2
       in (x:l, m, r)
    Just e2' ->
      let (l, m, r) = match xs e2'
       in (l, x:m, r)

subset xs ys = and [x `elem` ys | x <- xs]
equiv xs ys =    subset xs ys
              && subset ys xs

prop_match =
  forAll (arbitrary::Gen(String,String)) $ \(xs, ys) ->
      let (l, m, r) = match xs ys in
      ((l ++ m) `equiv` xs) && ((m ++ r) `equiv` ys)

exactlyOneDistinct [] = False
exactlyOneDistinct (x:xs) = all (==x) xs

matchesForConjE :: [Prop] -> [Prop] -> Bool
matchesForConjE e1 e2 =
  let (conjs, others) = partition isConj e1 in
  others `subset` e2 &&
  let interestingConjs = [Conj a b| Conj a b <- conjs, Conj a b `notElem` e2] in
  exactlyOneDistinct interestingConjs &&
  case interestingConjs of
    Conj a b : _ -> a `elem` e2 && b `elem` e2

  -- let (e1', common, e2') = match e1 e2 in
  -- case (e1', e2') of
  --     ([c `Conj` d], [a, b]) -> a == c && b == d
  --     (_, _) -> False

grab :: ProofProp -> Bool -> (Bool, ProofProp)
grab prop b = if b then (b, undefined) else (b, prop)
andThen (ba, pa) (bb, pb) = if not bb then (bb, pb) else
                           if not ba then (ba, pa) else
                             (True, undefined)

check :: ProofProp -> (Bool, ProofProp)
check pp@(Ass, env, prop) = grab pp $ prop `elem` env
check pp@(ConjI p1 p2, env, prop) =
  check p1 `andThen` check p2 `andThen`
  grab pp (propOf p1 `Conj` propOf p2 == prop &&
             envOf p1 `subset` env && envOf p2 `subset` env)
check pp@(ConjE p1, env, prop) =
  check p1 `andThen`
  (grab pp $
    propOf p1 == prop &&
    matchesForConjE env (envOf p1))
check pp@(DisjIL p1, env, prop) =
  check p1 `andThen`
  (grab pp $ case prop of
    Disj a b -> a == propOf p1
    _        -> False
   && envOf p1 `subset` env)
check pp@(DisjIR p1, env, prop) =
  check p1 `andThen`
  (grab pp $ case prop of
    Disj a b -> b == propOf p1
    _        -> False
   && envOf p1 `subset` env)
check pp@(ImplI p1, env, prop) =
  check p1 `andThen`
  (grab pp $ case prop of
    Impl a b -> b == propOf p1 &&
                (a:env) `subset` envOf p1
    _        -> False)
check pp@(ImplE p1 p2, env, prop) =  --  That p -> q   p   |   q
  -- TODO: Change this to expect a hypothesis p->q already in context.
  check p1 `andThen` check p2 `andThen`
  (grab pp $ case propOf p1 of
    Impl a b -> a == propOf p2 &&
                b == prop
   && envOf p1 `subset` env && envOf p2 `subset` env)
check pp@(DisjE p1 p2, env, prop) =
  check p1 `andThen` check p2 `andThen`
  (grab pp $
   propOf p1 == prop && propOf p2 == prop &&
   case envOf p1 `match` envOf p2 of
     ([p], common, [q]) -> ((p `Disj` q) : common) `equiv` env
     -- Hm, weird case:
     ([], common, []) ->
        or [True | vee <- env, case vee of Disj a b -> a == b && a `elem` common ; _ -> False]
        && noLongerThan [() | hyp <- common, hyp `notElem` env] 1)

noLongerThan [] n = n >= 0
noLongerThan (x:xs) n = n >= 0 && noLongerThan xs (n-1)

checkPlain = fst . check

z = Var "z"
y = Var "y"
x = Var "x"

---- The prover ----

firstSuccess :: [a] -> Maybe a
firstSuccess [] = Nothing
firstSuccess (x:_) = Just x

tryAss env p =
    if p `elem` env then return (Ass, env, p)
    else mzero

tryConjI env p =
  case p of
    Conj a b ->
      if size a <= size b then
        do pa <- prove env a
           pb <- prove env b
           return (ConjI pa pb, env, p)
      else
        do pb <- prove env b
           pa <- prove env a
           return (ConjI pa pb, env, p)
    _ -> mzero

tryImplI env p =
  case p of
    Impl a b -> do pb <- prove (a:env) b
                   return (ImplI pb, env, p)
    _ -> mzero

tryDisjIL env p =
  case p of
    Disj a b -> do pa <- prove env a
                   return (DisjIL pa, env, p)
    _ -> mzero

tryDisjIR env p =
  case p of
    Disj a b -> do pb <- prove env b
                   return (DisjIR pb, env, p)
    _ -> mzero

tryConjE env p =
  let (conjs, others) = partition isConj env in
  case conjs of
    (Conj a b : otherConjs) -> do pb <- prove (a : b : otherConjs ++ others) p
                                  return (ConjE pb, env, p)
    [] -> mzero

tryDisjE env p =
  let (disjs, others) = partition isDisj env in
  case disjs of
    (Disj a b : otherDisjs) -> do pa <- prove (a : otherDisjs ++ others) p
                                  pb <- prove (b : otherDisjs ++ others) p
                                  return (DisjE pa pb, env, p)
    [] -> mzero

tryImplE env p =
  foldr mplus mzero $
    foreach env $ \hypo ->
      case hypo of
           Impl a b | b == p -> do pa <- prove env a
                                   return (ImplE (Ass, env, Impl a b) pa, env, p)
           _ -> mzero

foreach xs f = map f xs

isDisj (Disj _ _) = True
isDisj _          = False

isConj (Conj _ _) = True
isConj _          = False

isImpl (Impl _ _) = True
isImpl _          = False

prove :: Env -> Prop -> Maybe ProofProp
prove env p =
    tryAss env p `mplus`
    tryConjI env p `mplus`
    tryImplI env p `mplus`
    tryConjE env p `mplus`
    tryDisjE env p `mplus`
    tryImplE env p `mplus`
    tryDisjIL env p `mplus`
    tryDisjIR env p `mplus`
    mzero

capSize k gen = sized $ \n -> resize (n `min` k) gen

prop_prove =
  forAll (capSize 4 arbitrary) $ \prop ->
      case prove [] prop of
        Nothing ->        "unproven" `collect` True
        Just proofProp -> prop `collect` checkPlain proofProp

subProofs (ImplI p) = [p]
subProofs (ImplE p1 p2) = [p1, p2]
subProofs (ConjI p1 p2) = [p1, p2]
subProofs (ConjE p1) = [p1]
subProofs (DisjIL p1) = [p1]
subProofs (DisjIR p1) = [p1]
subProofs (DisjE p1 p2) = [p1, p2]
subProofs Ass = []

prettyProof p = concat (map prettypp (subProofs p))

{-
TODO: Currently this doesn't display premises in any way.
Make this much cooler. Collate the premises so as to show
them all together

Here's what the nice pretty-print should look like:

| P -> R            [1]
| | Q -> R          [2]
| +----------------
| | | P \/ Q        [3]
| | +--------
| | | | P           [4] (destruct 3)
| | | +---
| | | | R     [by 1, 4]
| | | *
| | | | Q           [5] (destruct 3)
| | | +----
| | | | R     [by 2, 5]
| | | *
| | | R      [via 4, 5]
| | P \/ Q -> R
| (Q -> R) -> P \/ Q -> R
(P -> R) -> (Q -> R) -> P \/ Q -> R
-}
prettypp :: ProofProp -> String
prettypp (proof, env, p) =
  prettyProof proof ++ pretty p ++ "\n"


-- Tests

notP prop = F `Impl` prop
demorg = (notP x `Conj` notP y) `Impl` notP (x `Disj` y)

canProve x = Data.Maybe.isJust (prove [] x)

tests = TestList [
  test (assertBool "" (canProve demorg))
  ]

indent l str = concat (replicate l "| ") ++ str

newAssump p env =
  envOf p \\ env

bar l = concat $ replicate l "+ "

curtail [] = []
curtail [x] = []
curtail (x:xs) = x : curtail xs

prettyy :: Int -> ProofProp -> String
prettyy l (ImplI p, env, c) =
  -- Put the assumption here
  indent (l+1) (pretty (head (newAssump p env))) ++ "\n" ++
  indent l "+---\n" ++
  prettyy (l+1) p ++
  indent l "+\n" ++
  indent l (pretty c) ++ "\n"
prettyy l (ImplE p1 p2, env, c) =
  prettyy l p1 ++
  prettyy l p2 ++
  indent l (pretty c) ++ "\n"
prettyy l (ConjI p1 p2, env, c) =
  prettyy l p1 ++
  prettyy l p2 ++
  indent l (pretty c) ++ "\n"
prettyy l (ConjE p1, env, c) =
  prettyy l p1 ++
  indent l (pretty c) ++ "\n"
prettyy l (DisjIL p1, env, c) =
  prettyy l p1 ++
  indent l (pretty c) ++ "\n"
prettyy l (DisjIR p1, env, c) =
  prettyy l p1 ++
  indent l (pretty c) ++ "\n"
prettyy l (DisjE p1 p2, env, c) =
  prettyy l p1 ++
  prettyy l p2 ++
  indent l (pretty c) ++ "\n"
prettyy l (Ass, env, c) =
  indent l (pretty c) ++ "\n"
