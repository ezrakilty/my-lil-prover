module Entropy where

splitEntropyBit 0 = (0, 0)
splitEntropyBit 1 = (0, 1)
splitEntropyBit 2 = (1, 0)
splitEntropyBit 3 = (1, 1)

-- | Split the entropy source @q@ in half, returning a pair of such sources.
splitEntropy :: (Integral a) => a -> (a, a)
splitEntropy q | q < 4 = splitEntropyBit q
splitEntropy q =
  let (a, b) = splitEntropy (q `div` 4) in
  let (i, j) = splitEntropyBit (q `mod` 4) in
  (a*2 + i, b*2 + j)

-- | From the entropy source @q@, extract a number between 0 and @choices@.
takeEntropy choices q = q `divMod` choices
