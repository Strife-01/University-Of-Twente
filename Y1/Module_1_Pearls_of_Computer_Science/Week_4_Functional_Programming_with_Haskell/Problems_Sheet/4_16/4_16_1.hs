parse :: (Eq a, Num a) => a -> [a] -> Bool
parse _ [] = False
parse x (y:ys)
    | x == y = True
    | otherwise = parse x ys

-- list 1 is the list we want to check in the list 2
contains :: (Eq a, Num a) => [a] -> [a] -> Bool
contains [] ys = True
contains (x:xs) ys
    | False == parse x ys = False
    | otherwise = contains xs ys
