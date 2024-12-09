incr :: (Ord a, Num a) => [a] -> Bool
incr [] = True
incr [_] = True
incr (x:y:rest)
    | x > y = False
    | otherwise = incr (y:rest)
