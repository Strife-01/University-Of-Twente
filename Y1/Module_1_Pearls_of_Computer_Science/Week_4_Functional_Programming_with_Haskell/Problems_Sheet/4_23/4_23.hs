import Test.QuickCheck
import Data.List

bubble :: (Ord a, Eq a) => [a] -> [a]
bubble [] = []
bubble [x] = [x]
bubble (x:y:xs)
    | x > y = y : bubble(x:xs)
    | otherwise = x : bubble(y:xs)

bsort :: (Ord a, Eq a) => [a] -> [a]
bsort xs
    | sorted xs = xs
    | otherwise = bsort (bubble xs)
  where
    sorted [] = True
    sorted [_] = True
    sorted (x:y:xs) = x <= y && sorted (y:xs)

prop_bsort :: (Ord a, Eq a) => [a] -> Property
prop_bsort xs = xs /= [] ==> sort xs == bsort xs
