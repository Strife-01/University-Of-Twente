import string

CYPHER_TEXT = """
AP QYM MSX JOSN LRAC, QYM WSXSQWN LY TBWKC DZO NSYOFOJO USHRWB.
LRAC AC SX AWHYJDSXL PABKD KDWZ AX LRAC TYFEK KKCAQFWWXL.
DZO SMLESV TYFEK KKCAQFWWXL MSX TO XYMXV SF DZO HNX PAVW
ZJYNSVOV SF DZO VOVSUKLOV CWMLSGX UKDVWN TYFEK KKCAQFWWXL YF DZO
HOSBD MJIHDGQJKHRQ ZSQW YF MSXNKK.
K HKKCOYJN AC FOWNWN LY GZWX LRW ZVP XSDO. OO HBGFANW DZSK
ZSCKGGBV SF OFMJIHDWN XYJW SD LRW OFN GP LRAC EOKCSQW NWXGDWN SC
O. DZO HKKCOYJN ZKK LWOF OFMJIHDWN MCAXY DZO JCS MJIHDGCQCLOE
GADZ DZO KDSDWN JCS ZMLDSU WGNMVMC F KFN HETVAM WHHYFOFD W.
IGEJ DSCC SK DG GJSLO QYMB GGF ZQDZYF ZJYYBSW LRSD TBWKCC LRW
OFMJIHDAYF YX DZO HKKCOYJN AX GBVOJ DG BWKV DZO HNX PAVW.
KDDZYMQZ DZO JCS WGNMVMC F SK VSBYO AD ESYRL WSUW CWXKO LY LBQ
DG PSMLYJSRO AD. LY WKKO LRAC HBGMWCK, GW GGEDN DSCO LY HBGFANW
IGE OSLR LRW LWVGG KDSDWN SNVSLSGXSV JCS WGNMVA KTM SXV N ORAMZ
RSFW LWOF EKOV SF K UYEZDOLODI VSXPWBWXL MGXLOPD TEL DZKL RSFW
LWOF QWXWBSDWN OSLR LRW CSWW LSN JKFNGW HBAWW QWXWBSDGB SC OKK
EKOV DG QWXWBSDW X. EKQLW DZOQ RWVH IGE LY XKUDGBAJW X?
"""

LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

def clean_text(text):
    """Remove punctuation, spaces, and newlines from the text."""
    return text.translate(str.maketrans('', '', string.punctuation)).replace(" ", "").replace("\n", "")

def decrypt_vigenere(ciphertext, key):
    """Decrypt the ciphertext using the Vigenère cipher with the given key."""
    key_length = len(key)
    decrypted_text = []
    
    for i, char in enumerate(ciphertext):
        if char in LETTERS:  # Only decrypt letters
            key_char = key[i % key_length]
            key_shift = LETTERS.index(key_char)
            decrypted_char = LETTERS[(LETTERS.index(char) - key_shift) % 26]
            decrypted_text.append(decrypted_char)
        else:
            decrypted_text.append(char)  # Non-alphabetic characters are unchanged
    
    return ''.join(decrypted_text)

def find_key(known_word, cipher_text):
    """Find all possible keys that match the known word in the ciphertext."""
    cleaned_cipher = clean_text(cipher_text)
    length_known_word = len(known_word)
    possible_keys = set()  # Use a set to avoid duplicates

    for i in range(len(cleaned_cipher) - length_known_word + 1):
        # Extract a portion of the ciphertext equal to the length of the known word
        segment = cleaned_cipher[i:i + length_known_word]
        
        # Generate the key based on the current segment and the known word
        key = []
        for j in range(length_known_word):
            key_char = LETTERS[(LETTERS.index(segment[j]) - LETTERS.index(known_word[j])) % 26]
            key.append(key_char)
        
        possible_keys.add(''.join(key))  # Add the generated key to the set
    
    return possible_keys

known_word = "CRYPTO"
possible_keys = find_key(known_word, CYPHER_TEXT)

# Decrypt the ciphertext using the found keys
for key in possible_keys:
    decrypted_message = decrypt_vigenere(clean_text(CYPHER_TEXT), key)
    print(f"Key: {key}\nDecrypted Message: {decrypted_message}\n")

print(find_key(known_word, CYPHER_TEXT))
