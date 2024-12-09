matches :: (Eq a) => [a] -> [a] -> Bool
matches [] _ = True
matches _ [] = False
-- list pattern
matches (x:xs) (y:ys)
    | x == y = matches xs ys
    | otherwise = False

count_found :: (Eq a) => [a] -> [a] -> Int
count_found [] _ = 0
count_found _ [] = 0
count_found pattern (x:xs)
    | length xs < length pattern = 0
    | matches pattern (take (length pattern) (x:xs)) = 1 + count_found pattern xs
    | otherwise = count_found pattern xs
