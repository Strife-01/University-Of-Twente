import random
from math import factorial

# Generate a list of 20 random integers between 1 and 100
random_list = random.sample(range(1, 10101000), 20)

print(random_list)

def bubble_sort(arr):
    length = len(arr)
    swaps, max_pos = -1, length - 1
    while swaps != 0:
        swaps = i = 0
        while i < max_pos:
            if arr[i] > arr[i + 1]:
                arr[i], arr[i + 1] = arr[i + 1], arr[i]
                swaps += 1
            i += 1
        max_pos -= 1

def bubble_sort_(arr):
    length, swaps = len(arr), -1
    while swaps != 0:
        swaps = i = 0
        while i < length - 1:
            if arr[i] > arr[i + 1]:
                arr[i], arr[i + 1] = arr[i + 1], arr[i]
                swaps += 1
            i += 1

bubble_sort(random_list)
print(random_list)
print(1/factorial(200))
