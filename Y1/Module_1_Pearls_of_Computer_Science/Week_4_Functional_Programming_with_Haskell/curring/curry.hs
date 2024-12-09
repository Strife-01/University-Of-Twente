f1 :: (Num a) => a -> a -> a -> a
f1 x y z = x + y + z

f2 :: (Num a) => a -> a -> a
f2 = f1 2

f3 :: (Num a) => a -> a
f3 = f2 3

main :: IO ()
main = do
    let result = f3 1
    print result
