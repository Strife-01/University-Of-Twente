import Test.QuickCheck

mylength :: [a] -> Int
mylength [] = 0
mylength (_:xs) = 1 + mylength xs
prop_mylength xs = length xs == mylength xs

mysum :: Num a => [a] -> a
mysum [] = 0
mysum (x:xs) = x + mysum xs
prop_mysum xs = mysum xs == sum xs

myreverse :: [a] -> [a]
myreverse [] = []
myreverse (x:xs) = myreverse xs ++ [x]
prop_myreverse xs = myreverse xs == reverse xs

mytake :: Int -> [a] -> [a]
mytake n [] = []
mytake 0 xs = []
mytake n (x:xs) = [x] ++ mytake (n - 1) xs
prop_mytake n xs = n >= 0 ==> mytake n xs == take n xs

myelem x [] = False
myelem x (y:ys)
    | x == y = True
    | otherwise = myelem x ys
prop_myelem x ys = myelem x ys == elem x ys

myconcat :: [[a]] -> [a]
myconcat [] = []
myconcat (x:xs) = x ++ myconcat xs
prop_myconcat xs = xs /= [] ==> myconcat xs == concat xs

--mymaximum :: (Num a, Ord a) => [a] -> a
mymaximum [] = -1/0 -- -Inf
mymaximum (x:xs) =
    let y = mymaximum xs
    in if x >= y then x
    else y
prop_mymaximum xs = not (null xs) ==> mymaximum xs == maximum xs

myzip :: [a] -> [b] -> [(a,b)]
myzip [] _ = []
myzip _ [] = []
myzip (x:xs) (y:ys) = (x, y):myzip xs ys
prop_myzip xs ys = xs /= [] && ys /= [] ==> myzip xs ys == zip xs ys
