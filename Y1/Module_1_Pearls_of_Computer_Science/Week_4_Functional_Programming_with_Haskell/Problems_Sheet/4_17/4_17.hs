divisors 0 = []
divisors n = [x | x <- [1..n], n `mod` x == 0]
