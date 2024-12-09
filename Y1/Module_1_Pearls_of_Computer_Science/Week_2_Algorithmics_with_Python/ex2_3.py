def linear(data, value, reverse=False):
    """Return the index of 'value' in 'data', or -1 if it does not occur"""
    # Search in reverse same result
    if reverse == True:
        for index in range(len(data) - 1, -1, -1):
            if data[index] == value:
                return index
        return "does not occur"
    # Go through the data list from index 0 upwards
    i = 0 # if we start from 1 we lose data (first element)
    # continue until value found or index outside valid range
    while i < len(data) and data[i] != value: # if we change < to <= than if overflow we will have an error index out of range
        # increase the index to go to the next data value
        i = i + 1
    # test if we have found the value
    if i == len(data):
        # no, we went outside valid range; return -1
        return "doesn not occur"
    else:
        # yes, we found the value; return the index
        return i
