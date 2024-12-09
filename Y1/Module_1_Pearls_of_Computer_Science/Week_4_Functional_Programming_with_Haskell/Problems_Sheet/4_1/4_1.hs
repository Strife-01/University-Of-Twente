f x = 2 * x^2 + 3 * x - 5

main :: IO ()
main = do
    let x1 = f 10
    let x2 = f 11
    print x1
    print x2
