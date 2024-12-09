dotproduct :: (Num a) => [a] -> [a] -> a
dotproduct [] [] = 0
dotproduct xs [] = 0
dotproduct [] ys = 0
dotproduct (x:xs) (y:ys)
    | length xs /= length ys = 0
    | otherwise = x * y + dotproduct xs ys

