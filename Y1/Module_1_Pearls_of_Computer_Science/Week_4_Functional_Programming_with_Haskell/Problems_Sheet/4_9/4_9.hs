r :: Num a => a -> a -> Int -> a
r _ _ 0 = 0
r a _ 1 = a
r a d i = d + r a d (i - 1)

total :: (Num a, Ord a) => Int -> Int -> a -> a -> a
total i j a d
    | i == j + 1 = 0
    | otherwise = r a d i + total (i + 1) j a d
