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

#L = [1,1,1,2,3,4,4,55,66,66,"hei", "hei", "wowow", "wowo"]
#print(remove_dups(L))
    
