module Prop where

import Data.List (partition)
import Test.QuickCheck
import Control.Monad hiding (when, join)

import Entropy

type V = String

data Prop = T | F | Var V | Conj Prop Prop | Disj Prop Prop | Impl Prop Prop
    deriving (Eq, Show)
-- TODO: Get rid of T?

infixr 9 `Impl`

arbitraryVar :: [V] -> Gen V
arbitraryVar env =
  frequency [(1, return (head env)), (1, arbitraryVar (tail env))]

when b mx = if b then mx else mzero

instance Arbitrary Prop where
  arbitrary = sized $ \size -> oneof $ [
        -- return F,
        do x <- arbitraryVar standardEnv ; return (Var x)
    ] ++ when (size > 0) [
        resize (size `div` 2) (do a <- arbitrary ; b <- arbitrary ; return (a `Conj` b))
      , resize (size `div` 2) (do a <- arbitrary ; b <- arbitrary ; return (a `Disj` b))
      , resize (size `div` 2) (do a <- arbitrary ; b <- arbitrary ; return (a `Impl` b))
    ]

---- Pretty-printing ----

parenAt x y str | y < x = "(" ++ str ++ ")"
                | True  =        str

class Pretty a where
  pretty :: a -> String

prettyProp :: Int -> Prop -> String
prettyProp _ T = "True"
prettyProp _ F = "False"
prettyProp _ (Var name) = name
prettyProp l (Conj a b) =
  parenAt 0 l (prettyProp 0 a ++ " /\\ " ++ prettyProp 0 b)
prettyProp l (Disj a b) =
  parenAt 1 l (prettyProp 1 a ++ " \\/ " ++ prettyProp 1 b)
prettyProp l (Impl a b) =
  parenAt 2 l (prettyProp 1 a ++ " -> " ++ prettyProp 2 b)

instance Pretty Prop where
  pretty = prettyProp 2

standardEnv = ["p", "q", "r", "x", "y", "z", "s", "t", "u", "v"] ++ ["x"++show i | i <- [0..]]

extend env n =
  map snd (take n (dropWhile (\(x,y) -> x == y) (zip (env ++ repeat "") standardEnv)))

gen :: [V] -> Int -> Int -> Prop
gen env 0 q = if even q then T else F
gen env 1 q =
  if null env then gen env 0 q
  else
     Var (env !! (q `mod` length env))
gen env n q =
  let (remQ, inQ) = (q `divMod` 3) in
  let (leftQ, rightQ) = splitEntropy remQ in
  case inQ of
    0 ->
      let lefty = gen env (n-1) leftQ in
      let righty = gen env (n-1) rightQ in
      Conj lefty righty
    1 ->
      let lefty = gen env (n-1) leftQ in
      let righty = gen env (n-1) rightQ in
      Disj lefty righty
    2 ->
      let (remQ', newVars) = if n > length env then
                                remQ `divMod` (n - length env)
                             else (remQ, 0) in
      let (leftQ, rightQ) = splitEntropy remQ' in
      let newEnv = extend env newVars in
      let lefty = gen (env++newEnv) (n-1) leftQ in
      let righty = gen (env++newEnv) (n-1) rightQ in
        Impl lefty righty

hasConst T = True
hasConst F = True
hasConst (Var x) = False
hasConst (Conj a b) = hasConst a || hasConst b
hasConst (Disj a b) = hasConst a || hasConst b
hasConst (Impl a b) = hasConst a || hasConst b

size T = 0
size F = 0
size (Var x) = 1
size (Conj a b) = size a + size b + 1
size (Disj a b) = size a + size b + 1
size (Impl a b) = size a + size b + 1
