def memoization(func):
    cache = {}
    def inner(n, x):
        if n not in cache:
            cache[n] = func(n)
        return cache[n]
    return inner

@memoization
def fibo(n):
    return fibo(n - 1) + fibo(n - 2) if n > 2 else 1

print(fibo(500))

def fibo2(n):
    a = 0
    b = 1
    
    for _ in range(n):
        a, b = b, a + b

    return a
