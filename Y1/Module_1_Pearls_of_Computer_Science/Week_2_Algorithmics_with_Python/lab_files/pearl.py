import sort
import util
import dup

# match cases
#NORMAL_SEARCH = 1
#RECURRENCE_SEARCH = 2
#DENSITY_SEARCH = 3

#import random

#PAIRS_TEST = []
#PAIRS_TEST.extend([['dead', 'grail.txt']] * 3)
#PAIRS_TEST.extend([['spank', 'grail.txt']] * 7) 
#PAIRS_TEST.extend([["'eunt'", 'brian.txt']] * 2)
#PAIRS_TEST.extend([['dead', 'brian.txt']])
#PAIRS_TEST.extend([['vest', 'vest.txt']])
#PAIRS_TEST.extend([['vest1', 'vest.txt']])
#random.shuffle(PAIRS_TEST)

def make_table(pairs, option = 1):
    arr = None
    match option:
        case 1: 
            arr = dup.remove_dups_basic(sort.merge_sort(pairs))
        case 2:
            arr = dup.remove_dups_recurrence(sort.merge_sort(pairs))
        case 3: 
            arr = dup.remove_dups_density(sort.merge_sort(pairs))
        case _: 
            arr = dup.remove_dups_basic(sort.merge_sort(pairs))
    
    return arr
    #print(l)
    #return l

#test = make_table(PAIRS_TEST)
#print(test)
