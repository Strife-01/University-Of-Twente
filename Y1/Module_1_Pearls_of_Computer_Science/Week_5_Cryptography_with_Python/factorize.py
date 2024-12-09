def fact(N):
    factors = []
    factor, n_f = 2, 0
    while N:
        if N % factor == 0:
            n_f += 1
            N //= factor
            print(N)
        elif N == 1:
            if n_f > 0:
                factors.append((factor, n_f))
            break
        else:
            if n_f > 0:
                factors.append((factor, n_f))
            factor += 1
            n_f = 0
    return factors

num = int(input("Number to be factored: "))
factors = fact(num)

print(f"{num} = ", end="")
for f, n_f in factors:
    print(f"{f}^{n_f}", end=" * ")
print()

