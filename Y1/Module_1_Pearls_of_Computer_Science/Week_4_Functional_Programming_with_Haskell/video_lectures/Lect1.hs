f :: (Num a) => a -> a
f x = 2 * x^2 + 3 * x + 5

g :: (Num a) => a -> a -> a
g x y = f x + f y


