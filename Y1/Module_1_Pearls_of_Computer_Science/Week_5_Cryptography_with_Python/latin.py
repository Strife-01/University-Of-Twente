from collections import Counter

# Frequency of letters in English
fr = {
    'I': 10.73,
    'E': 10.26,
    'A': 9.33,
    'U': 9.02,
    'N': 8.4,
    'T': 7.93,
    'S': 6.69,
    'R': 5.44,
    'M': 5.29,
    'O': 5.13,
    'L': 4.67,
    'Q': 2.8,
    'G': 2.49,
    'C': 2.33,
    'P': 2.33,
    'D': 2.02,
    'B': 1.87,
    'F': 1.4,
    'H': 0.93,
    'V': 0.78,
    'X': 0.16
}

# Given text
text = """Tyccby kru esmbr zbvbry bm iypukr upkr, dfypfs fmys bmhecfmu Okctyk, ycbys Ydfbuymb, ukpubys dfb birepfs cbmtfy Hkcuyk, merupy Tyccb yiikccymufp. Lb esmkr cbmtfy, bmrubufubr, cktbofr bmukp rk zbxxkpfmu. Tyccer yo Ydfbuymbr Typfsmy xcfskm, y Okctbr Syupemy ku Rkdfymy zbvbzbu. Lepfs esmbfs xepubrrbsb rfmu Okctyk, ipeiukpky dfez y hfcuf yudfk lfsymbuyuk ipevbmhbyk cemtbrrbsk yorfmu, sbmbskdfk yz ker skphyuepkr rykik hesskymu yudfk ky dfyk yz kxxksbmymzer ymbser ikpubmkmu bsiepuymu, ipewbsbdfk rfmu Tkpsymbr, dfb upymr Plkmfs bmhecfmu, dfbofrhfs hemubmkmukp okccfs tkpfmu. Dfy zk hyfry Lkcvkubb dfedfk pkcbdfer Tyccer vbpufuk ipykhkzfmu, dfez xkpk heubzbymbr ipekcbbr hfs Tkpsymbr hemukmzfmu, hfs yfu rfbr xbmbofr ker ipelbokmu yfu birb bm kepfs xbmbofr okccfs tkpfmu."""

# Clean and count letter frequencies in the text
cleaned_text = ''.join(filter(str.isalpha, text)).upper()
letter_count = Counter(cleaned_text)
total_letters = sum(letter_count.values())

# Get frequency of letters in the text
text_frequency = {letter: count / total_letters * 100 for letter, count in letter_count.items()}

# Sort letters based on frequency
sorted_text_letters = sorted(text_frequency, key=text_frequency.get, reverse=True)
sorted_fr_letters = sorted(fr, key=fr.get, reverse=True)

# Create substitution mapping
substitution_map = {sorted_text_letters[i]: sorted_fr_letters[i] for i in range(min(len(sorted_text_letters), len(sorted_fr_letters)))}

# Substitute letters in the original text
substituted_text = ''.join(substitution_map.get(char, char) for char in text.upper())

print(substituted_text)
