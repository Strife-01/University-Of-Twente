pauses = [2, 4, 8]
whole_dur = 240000 / 202


for p in pauses:
    print(f"duration of a note is {whole_dur / p}")
    print(f'note with {p} pause needs {9/10 * (whole_dur / p)} ms and the pause between {1/10 * (whole_dur / p)}')
