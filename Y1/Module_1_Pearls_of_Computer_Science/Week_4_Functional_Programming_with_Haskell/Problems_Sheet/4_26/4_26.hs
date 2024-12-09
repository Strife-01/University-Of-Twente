import Test.QuickCheck
import Data.List

calculate_middle :: [a] -> Int
calculate_middle [] = -1
calculate_middle xs = floor(fromIntegral (length xs) / 2)

merge :: (Ord a, Eq a) => [a] -> [a] -> [a]
merge x [] = x
merge [] y = y
merge (x:xs) (y:ys)
    | x <= y = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

msort [] = []
msort [x] = [x]
msort xs =
    let middle = calculate_middle xs
        left = msort (take middle xs)
        right = msort (drop middle xs)
    in
        merge left right

prop_msort :: (Ord a, Eq a) => [a] -> Property
prop_msort xs = xs /= [] ==> sort xs == msort xs
