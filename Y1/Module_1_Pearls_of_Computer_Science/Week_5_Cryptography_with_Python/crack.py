def vigenere_decrypt(ciphertext, key):
    decrypted_text = []
    key_length = len(key)
    key_as_int = [ord(i) - ord('A') for i in key]
    ciphertext_int = [ord(i) - ord('A') for i in ciphertext if i.isalpha()]

    for i in range(len(ciphertext_int)):
        value = (ciphertext_int[i] - key_as_int[i % key_length]) % 26
        decrypted_text.append(chr(value + ord('A')))
    return ''.join(decrypted_text)

# Convert large numbers to keys
def number_to_key(number):
    return ''.join(chr(int(digit) + ord('A')) for digit in str(number))

# Ciphertext
ciphertext = (
    "AP QYM MSX JOSN LRAC, QYM WSXSQWN LY TBWKC DZO NSYOFOJO USHRWB. "
    "LRAC AC SX AWHYJDSXL PABKD KDWZ AX LRAC TYFEK KKCAQFWWXL. "
    "DZO SMLESV TYFEK KKCAQFWWXL MSX TO XYMXV SF DZO HNX PAVW "
    "ZJYNSVOV SF DZO VOVSUKLOV CWMLSGX UKDVWN TYFEK KKCAQFWWXL YF DZO "
    "HOSBD MJIHDGQJKHRQ ZSQW YF MSXNKK. "
    "K HKKCOYJN AC FOWNWN LY GZWX LRW ZVP XSDO. OO HBGFANW DZSK "
    "ZSCKGGBV SF OFMJIHDWN XYJW SD LRW OFN GP LRAC EOKCSQW NWXGDWN SC "
    "O. DZO HKKCOYJN ZKK LWOF OFMJIHDWN MCAXY DZO JCS MJIHDGCQCLOE "
    "GADZ DZO KDSDWN JCS ZMLDSU WGNMVMC F KFN HETVAM WHHYFOFD W. "
    "IGEJ DSCC SK DG GJSLO QYMB GGF ZQDZYF ZJYYBSW LRSD TBWKCC LRW "
    "OFMJIHDAYF YX DZO HKKCOYJN AX GBVOJ DG BWKV DZO HNX PAVW. "
    "KDDZYMQZ DZO JCS WGNMVMC F SK VSBYO AD ESYRL WSUW CWXKO LY LBQ "
    "DG PSMLYJSRO AD. LY WKKO LRAC HBGMWCK, GW GGEDN DSCO LY HBGFANW "
    "IGE OSLR LRW LWVGG KDSDWN SNVSLSGXSV JCS WGNMVA KTM SXV N ORAMZ "
    "RSFW LWOF EKOV SF K UYEZDOLODI VSXPWBWXL MGXLOPD TEL DZKL RSFW "
    "LWOF QWXWBSDWN OSLR LRW CSWW LSN JKFNGW HBAWW QWXWBSDGB SC OKK "
    "EKOV DG QWXWBSDW X. EKQLW DZOQ RWVH IGE LY XKUDGBAJW X?"
)

# List of large numbers
large_numbers = [
    96473750728194822265724956252718102713,
    55394086866555743142841731433115885563,
    55607800959008333997500404160891562647,
    103183222240832246367639689876909232721,
    81595675594617074625241781712689179295,
    132769281008271469023864575917196559889,
    13278393287992650160375140898405064704,
]

# Decrypt using each key derived from the large numbers
for number in large_numbers:
    key = number_to_key(number)
    decrypted_message = vigenere_decrypt(ciphertext, key)
    print(f"Decrypted with key '{key}': {decrypted_message}\n")
