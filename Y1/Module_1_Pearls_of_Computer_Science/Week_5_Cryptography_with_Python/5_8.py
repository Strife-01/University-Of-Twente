
cypher_text = "BLIECAIE"

def encrypt (m, k):
    return (3 * m + 2 * k) % 32

def to_n_bit_binary(num, n):
    # Format the number to binary and remove the '0b' prefix
    binary_str = bin(num)[2:]
    
    # Pad the binary string with leading zeros to make it n bits
    padded_binary_str = binary_str.zfill(n)
    
    # If the number is too large to fit in n bits, return an error message or the overflowed bits
    if len(padded_binary_str) > n:
        return "Error: Number exceeds n bits."
    
    return padded_binary_str
original_dict = {0: '-', 1: 'A', 2: 'B', 3: 'C', 4: 'D', 5: 'E', 6: 'F', 7: 'G', 8: 'H', 9: 'I', 10: 'J', 11: 'K', 12: 'L', 13: 'M', 14: 'N', 15: 'O'}
char_dict = {
  '-': 0,
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
}

con = [16,17,18,19,20,21,22,23,24,25,26]

for i in range(len(con)):
    print(to_n_bit_binary(encrypt(con[i], 13), 5))


