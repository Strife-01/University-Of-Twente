f :: (Ord a, Floating a) => a -> a -> a -> (a, a)
f a b c = (extrX, extrY)
    where
        discr a b c = b^2 - 4 * a * c
        extrX = -b / (2 * a)
        extrY = (-1 * discr a b c) / (4 * a)

-- main :: IO ()
-- main = do
    


-- delta = b^2 - 4ac
-- x1 = (-b + sqrt(delta)) / 2a
-- x2 = (-b - sqrt(delta)) / 2a
--
-- the quadratic has as max / min value (-b/2a, -delta/4a)
