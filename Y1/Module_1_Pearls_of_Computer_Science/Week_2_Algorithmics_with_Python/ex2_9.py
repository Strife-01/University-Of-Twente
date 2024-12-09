from lab_files.util import lines
from ex2_8 import binary_l as binary

words = lines("lab_files/Unabr.dict")
length = len(words)
print(binary(words, "eagle", 0, length - 1))
print(binary(words,"zygose", 0, length - 1))
