"""
Command-line script to invoke text file search

Usage: 'google'
Pearls of Computer Science, Week 2
"""

# standard module containing process_time function
import time
# read words from dictionary file
import util
# module demanded in the pearl assignment
import pearl

# read in text files
start = time.process_time()
word_pairs = util.all_word_pairs()
duration = time.process_time() - start
print("Time spent reading text files: {}".format(round(duration*1000000)))

# create search table
start = time.process_time()
user_choice = 0
while True:
    try:
        user_choice = int(input("\n*** - Please choose the search type you require - ***\n\nEnter:\n1 and press enter for normal search\n2 and press enter for recurrence search\n3 and press enter for density search\n\nInput: "))
        break
    except:
        print("Incorrect Option - Try Again")
        continue
word_table = pearl.make_table(word_pairs, user_choice)
duration = time.process_time() - start
print("Time spent creating search table: {}".format(round(duration*1000000)))
# search in the table
import ordsearch
# ask for the first word
key = input("Search term: ")
# continue as long as a word was typed
while key != "":
    # search in word table
    index = ordsearch.binary_pairs(word_table, key)
    # print the outcome
    if (index < 0):
        print("'{}' does not occur".format(key))
    else:
        print("'{}' occurs in {}".format(key, word_table[index][1]))
    # ask for the next word
    key = input("\nSearch term: ")
