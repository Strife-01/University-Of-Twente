remove [] = []
remove (x:[]) = x:[]
remove (x:y:rest) =
    -- if the elements are the same we skip the first element
    if x == y then remove (y:rest)
        -- if the elements are different we keep them
        else x:(remove(y:rest))

main :: IO()
main = do
    let clean_arr = remove([1,1,1,1,2,2,2,3,3,3,4,4,4,5,5,5])
    print clean_arr
