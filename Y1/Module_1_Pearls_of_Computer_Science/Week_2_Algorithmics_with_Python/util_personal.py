import sort
import dup
import string


file_1 = "lab_files/hacktest.txt"
file_2 = "lab_files/grail.txt"


def get_individual_words(file_name):
    with open(file_name, "r") as file:
        text = file.read()
        translator = str.maketrans('', '', string.punctuation)
        clean_text_list = text.translate(translator).split()
        sorted_text = sort.merge_sort(clean_text_list)
        unique_words = dup.remove_dups(sorted_text)
        #print(unique_words)
        return len(unique_words)


print(f"for {file_1} there are {get_individual_words(file_1)} unique words")
print(f"for {file_2} there are {get_individual_words(file_2)} unique words")

# if the list is unsorted then it removes only the dups if they are encountered next to eachother in the text
# in case of tuples it compares first the elem 0_t1 with 0_t2 and if 0_t1 respects the rule on 0_t2
# it returns True else if they are equal we go to 1_t1 or 1_t2 and check
# but if it doesn t respect it then it is False directly
