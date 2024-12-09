"""
Command-line script to invoke and profile linear and binary search

Usage: 'measure dict-file'
Pearls of Computer Science, Week 2
"""

# standard module to access command-line parameter list sys.argv
import sys
# standard module containing process_time function
import time

from ordsearch import linear
from ordsearch import binary

# read words from dictionary file
import util
words = util.lines(sys.argv[1])
length_words = len(words)

# ask for the first word
value = input("Search for first word? ")
# continue as long as a word was typed
while value != "":
    # measure time for linear searching
    lstart = time.process_time(); lresult = linear(words, value); lend = time.process_time()
    # time values are fractions of seconds;
    # multiply by a million and round to get microseconds
    ltime = round((lend - lstart) * 1000000)

    # measure time for binary searching
    bstart = time.process_time(); bresult = binary(words, value, 0, length_words - 1); bend = time.process_time()
    # time values are fractions of seconds;
    # multiply by a million and round to get microseconds
    btime = round((bend - bstart) * 1000000)

    # print the outcome
    if (lresult != bresult):
        print("results for linear and binary differ: {} versus {}".format(lresult, bresult))
    elif (lresult < 0):
        print("'{}' does not occur".format(value))
    else:
        print("'{}' occurs at position {}".format(value, lresult))
    # print the measured time
    print("linear search took {} micros to complete".format(ltime))
    print("binary search took {} micros to complete".format(btime))

    # ask for the next word
    value = input("\nSearch for next word? ")
