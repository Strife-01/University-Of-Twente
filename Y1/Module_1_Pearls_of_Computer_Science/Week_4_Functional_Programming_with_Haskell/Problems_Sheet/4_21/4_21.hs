indexes :: Int -> [a] -> [(a, Int)]
indexes _ [] = []
indexes i (x:xs) = (x, i) : indexes (i + 1) xs

elems :: (a, b) -> (a, b)
elems (a, b) = (a, b)

lsearch _ [] = -1
lsearch n (x:xs) =
    let (e, i) = elems x
    in if e == n then i else lsearch n xs

linsearch n [] = -1
linsearch n xs =
    let index_list = indexes 0 xs
    in lsearch n index_list

