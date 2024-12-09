import Data.Char

--palindrome :: (Eq a, Char a, Num a, Ord a) => [a] -> Bool
palindrome :: (Eq a) => [a] -> Bool
palindrome xs = xs == reverse xs
