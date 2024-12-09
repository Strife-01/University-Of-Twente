# Students: Andrei Ursachi s3351912 and Martin de Boer s3350142


# Google Assignment Explanation Files
## Usage: python google.py | python3 google.py
## Description:
The algorithm asks the user to choose between 3 types of search based on the 3 types of requirements:
- Option 1 - Normal Search
- Option 2 - Recurrence Search
- Option 3 - Density Search
In order to achieve this level of functionality the following provided files were mutated:
- google.py:
	- under the create search table we implemented an infinite loop which asks the user for 1 option, sanitizes it and only moves forward if the user responded correctly , otherwise it asks again
	- also make_table now needs 2 arguments, 1 being the word_pairs and the other being the choice * have to specify that the make_table function uses default argument so the second argument is optional 
		- reason for change: Convenience for the users and teachers to be able to easily select between the 3 tasks
- util.py:
	- added the function lines_words_number which is the same as lines and it is used to return the number of words in a file after reading it and splitting it into individual words based on " "
	- modified the function all_word_pairs to also after parsing each filename in the list of filenames we open it and call lines_words_number with the file name as argument, get the number of words in the file and then we assign that in a dictionary called __ WORDS __ FILE __.
		- reason for changes: convenience for correction and also efficiency
		- justifying the use of the dict. It is the same as having a list of the following [[file_name, nr_words]], but used for efficiency of constant time and also ease of bug fixes and readability

The following files and code was added for the achievement of the required functionality:
- pearl.py contains the make_table function which takes in a list of pairs and an option for how that list should be processed. All it does after selecting the option is to sort the pairs using the merge_sort algorithm and then removing the duplicates based on the option, then returning the new array as a complex data structure that can be parsed by the "google.py engine"
	- the file also contains the testing which can be done by de-commenting random, PAIRS_TEST, random.shuffle, rest and print test and running python peal, also de-commenting in dup.py the test_dict which contains the "dummy data" with the words in files for option 3
- dup.py contains a dictionary for testing but also the functions which perform the duplicate removal for the word_table creation. * all of them receive an array of the form [[word, file], [word, file] ... ] and return a different array based on the type of search required.
	- #### Clarification:
		- comparator is the arr[0] which is the word in [word, file]
		- they all loop between all the pairs in the array and if there is duplicate they process it accordingly and if it is a different word, they change the comparator
	- #### remove_dups_basic:
		-  will just ignore elements that are the same as the comparator and the same file or if there is not the same file they add another file to the list for the same word or add a new instance all together if the word is different
		- form: [[word, [file1, file2?, ...]], [...]]
	- #### remove_dups_recurrence:
		- this will also add another element in the file list, a new array which contains the file name and the number of occurrences of the word in that file. We start with 1 for obvious reasons and we increase from there. Also when we encounter a new word we sort the array of files for word based on the number of occurrences in files of the word in decreasing order. If we encounter it again we increase the appearance for each word
		- form: [[word, [[file1, occurrence], [file2, occurrence]]], [...]]
	- #### remove_dups_density:
		- it works similar to remove_dups_recurrence but the difference is that now before sorting the file by occurences we devide each value by the number of words in the file and we get the density
- ordsearch.py only contains the binary_pairs function which takes in an arr and a searched values and returns the index of the pair in the array or -1 if not present. The implementation is linear search and before any complaint, we checked if it makes a difference for the dataset to implement binary search and we cannot tell the difference so this is why we left it like this. It is only used to look something up the the data-structure created by us cause it searches based on word and returns in an instant (for the human eye)
