gauss_sum :: Int -> Int
gauss_sum 0 = 0
gauss_sum n = n + gauss_sum (n - 1)

main :: IO ()
main = do
    let result = gauss_sum 3
    print result
