f :: (Ord a, Floating a) => a -> a -> a -> (a, a)
f a b c
    | discr a b c >= 0 = (root1 a b c, root2 a b c)
    | otherwise = error "discriminant negative"
    where
        discr a b c = b^2 - 4 * a * c
        root1 a b c = (-b + sqrt(discr a b c)) / (2 * a)
        root2 a b c = (-b - sqrt(discr a b c)) / (2 * a)


-- main :: IO ()
-- main = do
    


-- delta = b^2 - 4ac
-- x1 = (-b + sqrt(delta)) / 2a
-- x2 = (-b - sqrt(delta)) / 2a
