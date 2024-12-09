

def char_to_bin(char):
    """Convert character to 8-bit binary string."""
    return format(ord(char), '05b')

def bin_to_char(binary):
    """Convert 8-bit binary string back to character."""
    return chr(int(binary, 2))

def encrypt_decrypt(text, key):
    """Encrypt or decrypt text using XOR with a 5-bit key."""
    key_length = len(key)
    result = []

    for i, char in enumerate(text):
        char_bin = char_to_bin(char)
        # Repeat the key to match the character's binary length
        key_bin = (key * ((len(char_bin) // key_length) + 1))[:len(char_bin)]
        # XOR operation
        encrypted_char_bin = ''.join('1' if char_bin[j] != key_bin[j] else '0' for j in range(len(char_bin)))
        result.append(bin_to_char(encrypted_char_bin))

    return ''.join(result)

# Define key and plaintext
key = '10101'  # 5-bit key
plaintext = "Hello"

# Encrypt
ciphertext = encrypt_decrypt(plaintext, key)
print("Ciphertext:", ciphertext)

# Decrypt (XORing again with the same function)
decrypted_text = encrypt_decrypt(ciphertext, key)
print("Decrypted Text:", decrypted_text)
