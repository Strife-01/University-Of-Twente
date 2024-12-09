def binary_pairs_(arr, searched):
    l = len(arr)
    if l == 0:
        return -1
    #if type(arr[0]) is not tuple:
    #    return -2
    index = 0
    while index < l:
        if arr[index][0] == searched:
            return index
        index += 1
    return -1


def binary_pairs(arr, searched):
    l = len(arr)
    if l == 0:
        return -1
    #if type(arr[0]) is not tuple:
    #    return -2
    index = 0
    while index < l:
        if arr[index][0] == searched:
            return index
        index += 1
    return -1

#x = [("Anne" ,7) ,("John" ,5) ,("Pete" ,9)]
#print(binary_pairs(x, "Brenda"))
#print(binary_pairs(x, "John"))
