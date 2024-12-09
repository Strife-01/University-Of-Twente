import sort
import lab_files.util as u
# import standard module with clock function
import time
# measure start and end time when executing command

#words = u.lines_w("lab_files/metamorphosis.txt")
#words = u.lines_w("lab_files/hacktest.txt")
words = u.lines_w("lab_files/Unabr.dict")

start = time.process_time();sorted = sort.merge_sort(words); end = time.process_time()
# subtract start from end time; multiply by 10ˆ6 and round to get micros
duration_1 = round(( end - start ) * 1000000)

start = time.process_time();sorted = sort.bubble_sort(words); end = time.process_time()
# subtract start from end time; multiply by 10ˆ6 and round to get micros
duration_2 = round(( end - start ) * 1000000)

#print(sorted)
print(duration_1)
print(duration_2)
