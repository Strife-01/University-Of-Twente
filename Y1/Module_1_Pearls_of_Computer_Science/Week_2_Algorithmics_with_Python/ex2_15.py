def merge_sort(arr, left, right):
    '''Mutates the original array'''
    if left >= right:
        return
    mid = (left + right) // 2
    merge_sort(arr, left, mid)
    merge_sort(arr, mid + 1, right)
    merge_arrays(arr, left, right)


def merge_arrays(arr, left, right):
    mid = (left + right) // 2
    l_arr, r_arr = arr[left:mid + 1], arr[mid + 1:right + 1]
    len_arr_1, len_arr_2 = len(l_arr), len(r_arr)
    i, j, k = 0, 0, left

    while i < len_arr_1 and j < len_arr_2:
        if l_arr[i] < r_arr[j]:
            arr[k] = l_arr[i]
            i += 1
        else:
            arr[k] = r_arr[j]
            j += 1
        k += 1

    while i < len_arr_1:
        arr[k] = l_arr[i]
        k += 1
        i += 1

    while j < len_arr_2:
        arr[k] = r_arr[j]
        j += 1
        k += 1


def merge_sort_2(arr):
    length = len(arr)
    if length == 0 or length == 1:
        return arr.copy()
    mid = length // 2
    fst, snd = merge_sort_2(arr[:mid]), merge_sort_2(arr[mid:])
    res, fi, si = [], 0, 0
    fst_l, snd_l = len(fst), len(snd)
    while fi < fst_l and si < snd_l:
        if fst[fi] < snd[si]:
            res.append(fst[fi])
            fi += 1
        else:
            res.append(snd[si])
            si += 1

    res.extend(fst[fi:])
    res.extend(snd[si:])

    return res
        

L = [123,1,23,4124124,4,2,90,1,22,33,2,124,547,345,345,34,3]
#L = [4,3,1,6,2,5]
new_l = merge_sort_2(L)
print(new_l)
