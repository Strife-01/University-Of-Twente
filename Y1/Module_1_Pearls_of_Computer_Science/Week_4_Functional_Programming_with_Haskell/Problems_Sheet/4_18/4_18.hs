prime :: Int -> Bool
prime 0 = False
prime 1 = False
prime 2 = True
prime n =
    let pot_divs = [2..floor(sqrt(fromIntegral(n)))]
        divs = [x | x <- pot_divs, n `mod` x == 0]
    in if length divs > 0 then False else True
