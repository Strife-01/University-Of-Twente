import Test.QuickCheck
import Data.List

quicksort :: (Ord a, Eq a) => [a] -> [a]
quicksort [] = []
quicksort (x:rest) = quicksort [y | y <-rest, y <= x] ++ [x] ++ quicksort [y | y <-rest, y > x]

prop_quicksort :: (Ord a, Eq a) => [a] -> Property
prop_quicksort xs = xs /= [] ==> sort xs == quicksort xs
