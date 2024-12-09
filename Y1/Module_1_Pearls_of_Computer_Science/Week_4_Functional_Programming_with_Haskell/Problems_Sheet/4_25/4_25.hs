import Data.List
import Test.QuickCheck

ins :: (Ord a, Eq a) => a -> [a] -> [a]
ins n [] = [n]
ins n (x:xs)
    | n <= x = n:x:xs
    | otherwise = x:(ins n xs)

isort :: (Ord a, Eq a) => [a] -> [a]
isort [] = []
isort (x:xs) = ins x (isort xs)

prop_isort :: (Ord a, Eq a) => [a] -> Property
prop_isort xs = xs /= [] ==> sort xs == isort xs
