f :: Int -> Int
f n =
    if n > 2 then f (n - 1) + f (n - 2)
    else 1


main :: IO()
main = do
    let fibo_elem1 = f(1)
    let fibo_elem2 = f(2)
    let fibo_elem3 = f(3)
    let fibo_elem4 = f(4)
    let fibo_elem5 = f(5)
    let fibo_elem6 = f(6)
    let fibo_elem7 = f(7)
    let fibo_elem8 = f(8)
    let fibo_elem9 = f(9)
    let fibo_elem10 = f(10)
    print fibo_elem1
    print fibo_elem2
    print fibo_elem3
    print fibo_elem4
    print fibo_elem5
    print fibo_elem6
    print fibo_elem7
    print fibo_elem8
    print fibo_elem9
    print fibo_elem10
