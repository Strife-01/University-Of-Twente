--allEqual :: (Num a, Ord a) => [a] -> Bool
allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual [_] = True
allEqual (x:y:xs) = (x == y) && allEqual (y:xs)

compute_dist :: Num a => [a] -> [a]
compute_dist [] = []
compute_dist [_] = []
compute_dist (x:y:xs) =
    let d = y - x
    in d : (compute_dist (y:xs))

isAS :: (Num a, Eq a) => [a] -> Bool
isAS [] = False
isAS [_] = False
isAS xs = allEqual (compute_dist xs)
