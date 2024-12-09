from sympy import gcd, mod_inverse

# Given moduli and encrypted password
A = 96473750728194822265724956252718102713
B = 55394086866555743142841731433115885563
C = 55607800959008333997500404160891562647
D = 103183222240832246367639689876909232721
N = 132769281008271469023864575917196559889
E = 81595675594617074625241781712689179295  
W = 13278393287992650160375140898405064704

# Function to find common factors
def find_common_factors(moduli, N):
    for mod in moduli:
        # Because the A,B,C and D were created from the same random generators they happen to share factors so we find the gratest common div between them and the N
        factor = gcd(mod, N)
        # If they are not coprime means that the factor is one of the factors for N as all of them have 2 factors (A, B, C, D, N)
        if factor != 1:
            # returns a tuple with the 2 factors
            return factor, N // factor
    # if it doesn't find the factors it returns none
    return None, None

# List of the moduli that were created the same way as N
moduli = [A, B, C, D]

# Find factors of N
p, q = find_common_factors(moduli, N)
if p and q:
    print(f"Factors of N: p = {p}, q = {q}")
else:
    print("No common factors found")
    exit()

# Compute the private key components
# Euler's Totient
phi = (p - 1) * (q - 1)
# d * E mod phi = 1
# d = E^(-1) mod phi
# d = E (phi(phi) - 1) mod phi
d = mod_inverse(E, phi)
print(f"Public Key (N, E) = ({N}, {E})")
print(f"Private Key d = {d}")
print(f"Encrypted password: {W}")
# Decrypt the password
password = pow(W, d, N) # when pow has 3 args it does the efficient algorithm for exp by default
print(f"Decrypted password: {password}")

# the alg for pow in this case is:
"""
def mod_exp (x, y, N):
    #It outputs x^y mod N
    r, b = 1, x
    while y > 0:
        if y % 2 == 1:
            r = r * b % N
        b = b * b % N
        y //= 2
    return r
"""
