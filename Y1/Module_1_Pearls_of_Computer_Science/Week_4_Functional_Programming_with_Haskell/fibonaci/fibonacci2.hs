f :: Int -> Int
f 1 = 1
f 2 = 1
f n = f (n - 1) + f (n - 2)

main :: IO()
main = do
    let n = f(10)
    print n
