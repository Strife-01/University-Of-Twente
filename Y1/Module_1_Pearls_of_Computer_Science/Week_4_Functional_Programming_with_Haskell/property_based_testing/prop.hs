import Test.QuickCheck

f :: (Num a) => a -> a -> a
f x y = x + y

prop_f :: (Ord a, Num a) => a -> a -> Property
prop_f x y = x > y ==> f x y == x + y

main :: IO()
main = quickCheck prop_f
