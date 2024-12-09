prime :: Int -> Bool
prime 0 = False
prime 1 = False
prime 2 = True
prime n =
    let pot_divs = [2..floor(sqrt(fromIntegral(n)))]
        divs = [x | x <- pot_divs, n `mod` x == 0]
    in if length divs > 0 then False else True

parse :: Int -> [Int] -> [Int] -> [(Int, Int)]
parse _ [] _ = []
parse _ _ [] = []
parse n (x:xs) ys = [(x, y) | y <- ys, x + y == n] ++ parse n xs ys


prime_sum_of_2 :: Int -> [(Int, Int)]
prime_sum_of_2 0 = [(0, 0)]
prime_sum_of_2 1 = [(0, 0)]
prime_sum_of_2 n =
    let prime_a = [x | x <- [1..n], prime x]
        prime_b = [x | x <- [1..n], prime x]
    in parse n prime_a prime_b

