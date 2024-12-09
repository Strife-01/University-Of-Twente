# Euclid Algorithm
def gcd (a, b):
    if b == 0:
        return a
    return gcd (b, a % b)



# Extended Euclid Algorithm
# return (t, x, y)
def e_gcd (a, b):
    if b == 0:
        return (a, 1, 0)
    x1, x2, y1, y2 = 0, 1, 1, 0
    while b > 0:
        q = a // b
        r = a % b
        x = x2 - q * x1
        y = y2 - q * y1
        a, b, x1, x2, y1, y2 = b, r, x, x1, y, y1
    return (a, x2, y2)
"""
a = int(input("a = "))
e = 2
while (res := gcd(a, e)) != 1:
    e += 1
print(f"e = {e}")
print(gcd(a, e))
"""

print(gcd(2,8))
