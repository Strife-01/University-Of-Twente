import random

def quicksort(arr, low, high):
    if low < high:
        partition_index = partition(arr, low, high)
        quicksort(arr, low, partition_index - 1)
        quicksort(arr, partition_index + 1, high)


def partition(arr, low, high):
    pivot = arr[high]
    i = low - 1
    for j in range(low, high):
        if arr[j] <= pivot:
            i += 1
            arr[i], arr[j] = arr[j], arr[i]
    arr[i + 1], arr[high] = arr[high], arr[i + 1]
    return i + 1

L = [random.randint(0, 100) for elem in range(10)]
print(L)
quicksort(L, 0, len(L) - 1)
print(L)
