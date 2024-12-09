-- list 1 is the list we want to check in the list 2
contains :: (Ord a, Eq a, Num a) => [a] -> [a] -> Bool
contains [] _ = True
contains _ [] = False
contains (x:xs) (y:ys)
    | x == y = contains xs ys
    | otherwise = contains (x:xs) ys
