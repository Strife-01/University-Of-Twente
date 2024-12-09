def bubble_sort(arr):
    length = len(arr)
    swaps = length
    while swaps > 0:
        swaps = 0
        for index in range(length - 1):
            if arr[index] > arr[index + 1]:
                swaps += 1
                arr[index], arr[index + 1] = arr[index + 1], arr[index]
