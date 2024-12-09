import Control.Monad (liftM3)
-- liftM2 generates all the psiisble combinations with the 3 lists
combinations :: [Int] -> [Int] -> [Int] -> [(Int, Int, Int)]
combinations = liftM3 (,,)

extractElements :: (a, b, c) -> (a, b, c)
extractElements (x, y, z) = (x, y, z)

return_tuple :: Int -> [(Int, Int, Int)] -> [(Int, Int, Int)]
return_tuple _ [] = []
return_tuple n (tup:rest) =
    let (a, b, c) = extractElements tup
    in if a^2 + b^2 == c^2 && c <= n then (a, b, c) : return_tuple n rest
    else return_tuple n rest

pyth :: Int -> [(Int, Int, Int)]
pyth 0 = []
pyth n = return_tuple n (combinations [1..n] [1..n] [1..n])
    
