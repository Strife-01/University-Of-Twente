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


L = [1126312,6,2134,62136,213,6,213,62,136,123,76,638,54,87564,827,46,24357,34572,6,856,94765,35,84,756,3,465,46732,573,84654,7236,758,675,264]
print(L)
quicksort(L, 0, len(L) - 1)
print(L)
print(L == sorted(L))
