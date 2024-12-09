def mod_exp (x, y, N):
    """
        It outputs x^y mod N
    """
    r, b = 1, x
    while y > 0:
        if y % 2 == 1:
            r = r * b % N
        b = b * b % N
        y //= 2
    return r

print(mod_exp(8, 11, 35))
