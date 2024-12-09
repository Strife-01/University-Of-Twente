import Test.QuickCheck
import Data.List

hoSort :: (Ord a, Eq a) => (a -> (a -> Bool)) -> [a] -> [a]
hoSort r [] = []
hoSort r (x:rest) = hoSort r [y | y <-rest, r y x] ++ [x] ++ hoSort r [y | y <-rest, not (r y x)]

{-
prop_quicksort :: (Ord a, Eq a) => [a] -> Property
prop_quicksort xs = xs /= [] ==> sort xs == quicksort xs
-}
