def insert (arr):
    for i in range(1, len(arr)):
        for j in range(i, 0, -1):
            if arr[j] < arr[j-1]: arr[j], arr[j-1] = arr[j-1], arr[j]
            else: break

l = [435,1234,1235,341,6,23,71,3476,3,478,4368965274,3613,5,34,67836,58,35426,3142,6,3245,2345]
ls = [435,1234,1235,341,6,23,71,3476,3,478,4368965274,3613,5,34,67836,58,35426,3142,6,3245,2345]

insert(l)
print(l == sorted(ls))
print(l)
