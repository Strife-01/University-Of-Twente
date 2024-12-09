increment [] = []
increment (x:[]) = (x+1):[]
increment (x:rest) = (x+1):(increment(rest))

main :: IO()
main = do
    let first = [1,2,3,4,5]
    let incremented = increment(first)
    print first
    print incremented
