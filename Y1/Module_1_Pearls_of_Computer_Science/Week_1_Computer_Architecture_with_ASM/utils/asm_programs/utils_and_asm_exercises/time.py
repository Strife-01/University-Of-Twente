fr_note = 8554455.445544556
fr_pause = 950495.0495049505

e5 = 440

time_on = 12
time_off = 12

rebranch_time = 4

time_hog_on_off = 1 / (e5 * 2) * 16000000
print(f'hog_half = {time_hog_on_off}')


fr_note_up_or_down = fr_note / 2

print(fr_note / (time_on + time_off + 2 * time_hog_on_off + rebranch_time))
print(fr_pause / (time_on + time_off + 2 * time_hog_on_off + rebranch_time))
