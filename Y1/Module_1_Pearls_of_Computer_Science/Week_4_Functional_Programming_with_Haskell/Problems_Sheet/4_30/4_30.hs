import Test.QuickCheck
import Data.List

hoSort :: (Ord a, Eq a) => (a -> (a -> Bool)) -> [a] -> [a]
hoSort r [] = []
hoSort r (x:rest) = hoSort r [y | y <-rest, r y x] ++ [x] ++ hoSort r [y | y <-rest, not (r y x)]

all_pairs :: [(Int, Int)]
all_pairs = [(a, b) | a <- [1..6], b <- [1..6]]

all_pairs_with_n :: Int -> [(Int, Int)]
all_pairs_with_n n = [(a, b) | (a, b) <- pairs, a == n || b == n]
  where
    pairs = [(a, b) | a <- [1..6], b <- [1..6]]

sum_m :: Int -> [(Int, Int)]
sum_m m = [(x, y) | (x, y) <- all_pairs, x + y == m]

{-
generatepairswithsum :: [(Int, (Int, Int))]
generatepairswithsum = [(s, (a, b)) | s <- [2..12], (a, b) <- sum_m s]
  where
    sum_m m = [(x, y) | (x, y) <- all_pairs, x + y == m]
-}
all_pairs_sorted_by_sum = [(a, b) | (_, (a, b)) <- hoSort (<) [(s, (a, b)) | s <- [2..12], (a, b) <- sum_m s]]
  where
    all_pairs = [(a, b) | a <- [1..6], b <- [1..6]]
    sum_m m = [(x, y) | (x, y) <- all_pairs, x + y == m]
-- prop_hoSort :: (Ord a, Eq a) => (a -> a -> Bool) -> [a] -> Property
-- prop_hoSort r xs = xs /= [] ==> sort xs == hoSort r xs

