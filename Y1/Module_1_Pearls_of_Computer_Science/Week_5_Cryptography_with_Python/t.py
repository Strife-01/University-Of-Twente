# Ciphertext
cipher_text = "BLIECAIE"

# Character mappings
char_to_num_ = {'-': 0, 'A': 1, 'B': 2, 'C': 3, 'D': 4, 'E': 5, 
                'F': 6, 'G': 7, 'H': 8, 'I': 9, 'J': 10, 'K': 11, 
                'L': 12, 'M': 13, 'N': 14, 'O': 15}

char_to_num = {
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

num_to_char = {v: k for k, v in char_to_num.items()}

# Constants
IV = 2  # Initialization vector
k = 13  # Key
n_blocks = len(cipher_text)

# Encryption function
def encrypt(m, k):
    return (3 * m + 2 * k) % 32

# Decrypting the ciphertext
decrypted_text = ""
for j in range(n_blocks):
    CTR_j = j  # Counter starts from 0 to 7
    # Create block value by concatenating IV and CTR
    block_value = (IV << 3) | CTR_j  # IV in the upper bits, counter in the lower
    encrypted_value = encrypt(block_value, k)
    
    # Get numeric value for cipher character
    c_value = char_to_num[cipher_text[j]]  # This might throw KeyError if not present
    
    # XOR to decrypt
    m_value = (c_value ^ encrypted_value) % 32
    
    # Convert back to character
    decrypted_text += num_to_char.get(m_value, '?')  # Use '?' for any unknown mappings

print("Decrypted text:", decrypted_text)
