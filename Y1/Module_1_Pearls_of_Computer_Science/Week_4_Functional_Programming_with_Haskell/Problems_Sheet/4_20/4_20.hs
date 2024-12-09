perfect :: Int -> Bool
perfect 0 = False
perfect 1 = False
perfect n =
    let divisors = [x | x <- [1..n `div` 2], n `mod` x == 0]
    in sum divisors == n

perfect_unitll_n 0 = []
perfect_unitll_n 1 = []
perfect_unitll_n n = [x | x <- [1..n], perfect x]