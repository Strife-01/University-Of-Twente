"""Remove duplicates from sorted arrays"""
def remove_dups(arr):
    res, length = [], len(arr)
    if length != 0:
        comparator = arr[0]
        res.append(comparator)
        for i in range(1, length):
            if arr[i] != comparator:
                comparator = arr[i]
                res.append(comparator)
    return res

