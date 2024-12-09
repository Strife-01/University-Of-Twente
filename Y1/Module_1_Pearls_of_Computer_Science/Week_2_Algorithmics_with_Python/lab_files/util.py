"""
Utility functions for Pearls of Computer Science, Week 2
"""

def lines(filename):
    """Return list of lines from the file called filename"""
    words = []
    # open the dictionary file
    with open(filename, encoding="utf-8") as f:
        # assign the list of lines from f to words
        for w in f:
            # cut off line separator at end
            words.append(w[0:len(w) - 1])
    return words


def lines_w(filename):
    """Return list of lines from the file called filename"""
    words = []
    # open the dictionary file
    with open(filename, encoding="utf-8") as f:
        # assign the list of lines from f to words
        for w in f:
            # cut off line separator at end
            words.extend(w[0:len(w) - 1].split())
    return words


def lines_words_number(filename):
    """Return the number of words in a file"""
    words = []
    # open the dictionary file
    with open(filename, encoding="utf-8") as f:
        # assign the list of lines from f to words
        for w in f:
            # cut off line separator at end
            words.extend(w[0:len(w) - 1].split())
            #print(words)
    return len(words)



# library used for formatted reading
import csv

def words(filename):
    """Return list of space-separated words from the file called filename"""
    words = []
    # open the dictionary file
    with open(filename, encoding="utf-8") as f:
        # assign the list of lines from f to words
        for w in csv.reader(f, delimiter=' '):
			# note that w is a list of words, so extend rather than append
            words.extend(w)
    return words

def word_pairs(filenames):
	"""Return list of word + filename tuples from multiple files"""
	# list to collect resulting pairs
	result = []
	# go over all filenames
	for f in filenames:
		# go over all words in f
		for w in words(f):
			# add word+filename pair to result
			result.append([w,f])
	return result

# module with filename utils
import os
__WORDS__FILE__ = {}


def all_word_pairs():
    """Return list of word + filename tuples from .txt files in current directory"""
    # collect .txt filenames
    filenames = []

    # scan all files in current directory
    for f in os.listdir("."):
        # test if f ends with .txt
        if f.endswith(".txt"):
            # yes it does, so add it to filenames
            filenames.append(f)
            #with open(f, "r") as file:
            #    words = file.read().split(' ')
            #    __WORDS__FILE__[f] = len(words)
            __WORDS__FILE__[f] = lines_words_number(f)
            #print(__WORDS__FILE__)
    # collect word pairs from all filenames
    return word_pairs(filenames)
