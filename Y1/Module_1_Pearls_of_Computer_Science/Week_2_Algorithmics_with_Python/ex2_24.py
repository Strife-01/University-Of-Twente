import sort
import util

def make_table(pairs):
    sorted_list = sort.merge_sort(pairs)
    print(pairs)

make_table(util.all_word_pairs())
