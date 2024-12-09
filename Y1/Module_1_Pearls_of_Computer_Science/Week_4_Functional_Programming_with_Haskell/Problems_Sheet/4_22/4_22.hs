linsearch _ [] = []
linsearch n xs = [i | (x, i) <- zip xs [0..], x == n]
