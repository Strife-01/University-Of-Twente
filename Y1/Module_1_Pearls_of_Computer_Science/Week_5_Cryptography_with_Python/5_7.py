cypher_text = "BPYVZXPTAA-P_.,CPGF,ALZSABP.APU-,R-APV-I-_XT.AZ_V-KE"

def to_n_bit_binary(num, n):
    # Format the number to binary and remove the '0b' prefix
    binary_str = bin(num)[2:]
    
    # Pad the binary string with leading zeros to make it n bits
    padded_binary_str = binary_str.zfill(n)
    
    # If the number is too large to fit in n bits, return an error message or the overflowed bits
    if len(padded_binary_str) > n:
        return "Error: Number exceeds n bits."
    
    return padded_binary_str
original_dict = {0: '_', 1: 'A', 2: 'B', 3: 'C', 4: 'D', 5: 'E', 6: 'F', 7: 'G', 8: 'H', 9: 'I', 10: 'J', 11: 'K', 12: 'L', 13: 'M', 14: 'N', 15: 'O', 16: 'P', 17: 'Q', 18: 'R', 19: 'S', 20: 'T', 21: 'U', 22: 'V', 23: 'W', 24: 'X', 25: 'Y', 26: 'Z', 27: '.', 28: ',', 29: '-', 30: '!', 31: '?'}
char_dict = {
  '_': 0,
'A': 1,
'B': 2,
'C': 3,
'D': 4,
'E': 5,
'F': 6,
'G': 7,
'H': 8,
'I': 9,
'J': 10,
'K': 11,
'L': 12,
'M': 13,
'N': 14,
'O': 15,
'P': 16,
'Q': 17,
'R': 18,
'S': 19,
'T': 20,
'U': 21,
'V': 22,
'W': 23,
'X': 24,
'Y': 25,
'Z': 26,
'.': 27,
',': 28,
'-': 29,
'!': 30,
'?': 31,
}
#for index, c in enumerate(cypher_text):
#    if index % 5 == 0 and index != 0: print()
#    print(f"{c} - {to_n_bit_binary(char_dict[c], 5)}")
for i in range(32):
    print(f"key {i} - ", end="")
    for c in cypher_text:
        print(f"{original_dict[char_dict[c] ^ i]}", end="")
    print()

print(len(cypher_text))
