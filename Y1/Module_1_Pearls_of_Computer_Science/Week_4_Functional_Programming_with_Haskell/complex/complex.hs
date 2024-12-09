complex_mul :: (Num a) => (a, a) -> (a, a) -> (a, a)
complex_mul (x1, y1) (x2, y2) = (a, b)
    where
        a = x1 * x2 - y1 * y2
        b = x1 * y2 + x2 * y1

complex_add :: (Num a) => (a, a) -> (a, a) -> (a, a)
complex_add (x1, y1) (x2, y2) = (a, b)
    where
        a = x1 + x2
        b = y1 + y2

main :: IO ()
main = do
    let complex1 = (1, 2)
    let complex2 = (2, 3)
    let result_mul = complex_mul complex1 complex2
    let result_add = complex_add complex1 complex2
    print result_mul
    print result_add
