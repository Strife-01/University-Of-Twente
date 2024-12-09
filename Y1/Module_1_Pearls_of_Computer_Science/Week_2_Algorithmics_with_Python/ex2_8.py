def binary_r(data, value, left, right):
    """Binary search recursively"""
    if left < right:
        mid = (left + right) // 2
        if data[mid] == value:
            return mid
        elif data[mid] > value:
            return binary_r(data, value, left, mid - 1)
        else:
            return binary_r(data, value, mid + 1, right)
    return "Non existent in the list of values"

def binary_l(data, value, left, right):
    """Binary search lineary"""
    while left < right:
        mid = (left + right) // 2
        if data[mid] == value:
            return mid
        elif data[mid] > value:
            right = mid - 1
        else:
            left = mid + 1
    return "Non existent in the list of values"


