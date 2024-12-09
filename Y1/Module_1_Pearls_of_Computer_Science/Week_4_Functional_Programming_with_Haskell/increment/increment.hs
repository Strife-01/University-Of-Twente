increment :: Int -> IO()
increment x =
    if x <= 100 then do
        print x
        increment (x + 5)
    else
        print x

main :: IO()
main = do
    let x = 0
    increment x
