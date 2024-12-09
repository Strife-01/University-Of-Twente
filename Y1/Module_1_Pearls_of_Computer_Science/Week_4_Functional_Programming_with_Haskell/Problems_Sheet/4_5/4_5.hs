import Data.Char

-- we need a character
isEnLower :: Char -> Bool
isEnLower x = ord x >= 97 && ord x <= 122

isEnUpper :: Char -> Bool
isEnUpper x = ord x >= 65 && ord x <= 90
