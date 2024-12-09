itn :: (a -> a) -> a -> Int -> a
-- function value nr_times
itn f a 1 = f a
itn f a n = itn f (f a) (n - 1)
