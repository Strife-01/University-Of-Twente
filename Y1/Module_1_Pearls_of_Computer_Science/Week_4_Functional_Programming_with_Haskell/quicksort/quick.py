"""
def quicksort (arr):
    length = len(arr)
    if length > 1:
        pivot = arr[length - 1]
        left = []
        right = []
        for i in range(length - 1):
            if arr[i] <= pivot: left.append(arr[i])
            else: right.append(arr[i])
        return quicksort(left) + [pivot] + quicksort(right)
    return arr
"""

def quicksort(arr, low, high):
    if low < high:
        pivot_index = partition(arr, low, high)
        quicksort(arr, low, pivot_index - 1)
        quicksort(arr, pivot_index + 1, high)

def partition(arr, low, high):
    pivot = arr[high]
    i = low - 1
    for j in range(low, high):
        if arr[j] <= pivot:
            i += 1
            arr[i], arr[j] = arr[j], arr[i]
    arr[i + 1], arr[high] = arr[high], arr[i + 1]
    return i + 1

L = [12,3,12,21,4,124,21,5,3,325,321]
print(L)
quicksort(L, 0, len(L) - 1)

print(L)
