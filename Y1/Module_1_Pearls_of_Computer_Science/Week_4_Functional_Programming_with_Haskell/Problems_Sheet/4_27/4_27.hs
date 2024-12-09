quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
-- ++ is list concatenation
-- x is the pivot
-- we return an arr that is concatenated on left < midd x and right >
quicksort (x:rest) = left ++ [x] ++ right
    where
        -- list comprehention 
        left = quicksort [a | a <- rest, a < x]
        right = quicksort [a | a <- rest, a > x]

