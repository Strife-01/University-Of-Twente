def binary_pairs(arr, searched):
    if len(arr) == 0:
        return -1
    if type(arr[0]) is not tuple:
        return -2
    for v1, v2 in arr:
        if v1 == searched:
            return arr.index((v1,v2))
    return -1

#x = [("Anne" ,7) ,("John" ,5) ,("Pete" ,9)]
#print(binary_pairs(x, "Brenda"))
#print(binary_pairs(x, "John"))
