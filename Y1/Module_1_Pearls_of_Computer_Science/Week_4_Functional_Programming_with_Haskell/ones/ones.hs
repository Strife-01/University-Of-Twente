take_ 0 _ = []
take_ _ [] = []
take_ n (x:xs) = x : take (n - 1) xs

ones = 1 : ones

--take 2 ones
