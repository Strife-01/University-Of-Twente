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

main :: IO ()
main = do
    let unordered = [12,456,213,12,421,4,21,4,21,412,5,321,5623,16,3216,123,4213,41]
    let ordered = quicksort (unordered)
    print unordered
    print ordered
