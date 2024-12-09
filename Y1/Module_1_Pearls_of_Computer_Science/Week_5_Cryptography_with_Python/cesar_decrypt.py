CHYPER_TEXT = "EBOBFPXKBKDIFPEPBKQBKZBQEXQZLKQXFKPJLOBLCQEBIBQQBOBQEXKLCXKVLQEBOIBQQBO"

def cesar_dec(cypher_text, key):
    decyphered = ""
    for letter in cypher_text.upper():
        ascii_rep = ord(letter)
        decyphered += chr((ascii_rep - ord('A') - key) % 26 + ord('A'))
    print(f"key = {key}, plaintext = {decyphered}")


for key in range(26):
    cesar_dec(CHYPER_TEXT, key)
