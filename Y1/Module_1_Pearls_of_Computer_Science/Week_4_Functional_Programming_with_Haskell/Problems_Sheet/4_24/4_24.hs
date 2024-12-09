import Test.QuickCheck
import Data.List

-- minimum
-- maximum

mmsort :: (Ord a, Eq a) => [a] -> [a]
mmsort [] = []
mmsort [x] = [x]
mmsort xs = minn : mmsort (xs \\ [minn, maxx]) ++ [maxx]
  where
    minn = minimum xs
    maxx = maximum xs

prop_mmsort :: (Ord a, Eq a) => [a] -> Property
prop_mmsort xs = xs /= [] ==> sort xs == mmsort xs
