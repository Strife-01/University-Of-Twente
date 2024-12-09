def linear(data, value):
    """We assume that the list of values is sorted"""
    index = 0
    length = len(data)
    while index < length:
        if value < data[index]:
            return "not in list"
        elif value == data[index]:
            return index
        index += 1

# if we are searching for a word in a list of numbers
# or vice versa we will get an error of comparison

