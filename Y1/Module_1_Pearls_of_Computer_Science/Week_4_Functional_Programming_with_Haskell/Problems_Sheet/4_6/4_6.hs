import Test.QuickCheck
-- 1 + 2 + 3 + 4 + 5 = 15

total1 :: Int -> Int
total1 0 = 0
total1 n = total1 (n - 1) + n

-- 5 * 6 / 2 = 15
total2 :: Int -> Int
total2 n = (n * (n + 1)) `div` 2

prop_total n = (n >= 0) ==> total1 n == total2 n
