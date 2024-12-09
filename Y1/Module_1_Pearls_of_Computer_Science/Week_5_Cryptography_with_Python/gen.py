
def mod_exp(x, y, N):
    """
        It outputs x^y mod N
    """
    r = 1
    b = x % N  # Ensure base is within modulo
    while y > 0:
        if y % 2 == 1:  # If y is odd
            r = (r * b) % N
        b = (b * b) % N  # Square the base
        y //= 2  # Divide y by 2
    return r

result = mod_exp(34, 581, 143)
print(result)
