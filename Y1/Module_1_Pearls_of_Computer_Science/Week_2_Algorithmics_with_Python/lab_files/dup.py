import sort
from util import __WORDS__FILE__ as words_count

#test_dict = {
#    'brian.txt': 3,
#    'grail.txt': 10,
#    'vest.txt': 2
#}


"""Remove duplicates from sorted arrays"""
def remove_dups_basic(arr):
    res, length, index = [], len(arr), 0
    if length != 0:
        comparator = arr[0]
        res.append([comparator[0],[comparator[1]]])
        for i in range(1, length):
            if arr[i][0] != comparator[0]:
                comparator = arr[i]
                res.append([comparator[0], [comparator[1]]])
                index += 1
            else:
                if arr[i][1] not in res[index][1]:
                    res[index][1].append(arr[i][1])
    return res


"""Remove duplicates from sorted arrays and counts the appearences"""
def remove_dups_recurrence(arr):
    res, length, index = [], len(arr), 0
    if length != 0:
        comparator = arr[0]
        res.append([comparator[0],[[comparator[1], 1]]])
        for i in range(1, length):
            if arr[i][0] != comparator[0]:
                comparator = arr[i]
                res.append([comparator[0], [[comparator[1], 1]]])
                res[index][1] = sort.merge_sort_especiale(res[index][1])
                #print(res[index], end="\n\n")
                index += 1
                # in case of last element we need to count another time
                if i == length:
                    res[index][1] = sort.merge_sort_especiale(res[index][1])
            else:
                l = len(res[index][1])

                for j in range(l):
                    if arr[i][1] == res[index][1][j][0]:
                        res[index][1][j][1] += 1
                        break
                else:
                    res[index][1].append([arr[i][1], 1])
    return res

"""Remove duplicates from sorted arrays and counts the density of the word"""
def remove_dups_density(arr):
    res, length, index = [], len(arr), 0
    if length != 0:
        comparator = arr[0]
        res.append([comparator[0],[[comparator[1], 1]]])
        for i in range(1, length):
            if arr[i][0] != comparator[0]:
                comparator = arr[i]
                res.append([comparator[0], [[comparator[1], 1]]])
                l = len(res[index][1])
                for j in range(l):
                    res[index][1][j][1] /= words_count[res[index][1][j][0]]
                    #res[index][1][j][1] /= test_dict[res[index][1][j][0]]
                    #print(res[index][1][j][1], words_count[res[index][1][j][0]])
                res[index][1] = sort.merge_sort_especiale(res[index][1])
                #print(res[index], end="\n\n")
                index += 1
                # in case of the last element we have to perform a special count
                if i == length - 1:
                    l = len(res[index][1])
                    for j in range(l):
                        res[index][1][j][1] /= words_count[res[index][1][j][0]]
                        #res[index][1][j][1] /= test_dict[res[index][1][j][0]]
                        #print(res[index][1][j][1], words_count[res[index][1][j][0]])
                    res[index][1] = sort.merge_sort_especiale(res[index][1])

            else:
                l = len(res[index][1])

                for j in range(l):
                    if arr[i][1] == res[index][1][j][0]:
                        res[index][1][j][1] += 1
                        break
                else:
                    res[index][1].append([arr[i][1], 1])
    return res
#L = ['hello', 'hello', 'hi', 'world', 'world', 'world']
#print(remove_dups_count(L))


