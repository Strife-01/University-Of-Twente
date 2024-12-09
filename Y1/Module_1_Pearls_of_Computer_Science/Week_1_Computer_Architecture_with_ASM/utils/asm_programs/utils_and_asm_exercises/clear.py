import re

with open('compute_times.py', 'r') as fhead:
    for line in fhead:
        with open('correct.py', 'a') as fwrite:
            line_list = re.split('\s+', line)
            if line_list[0].strip() == '#define':
                fwrite.write(f'\t\'{line_list[1]}\': {line_list[2]},\n')
            else:
                line_list.append('\n')
                fwrite.write(''.join(line_list))

