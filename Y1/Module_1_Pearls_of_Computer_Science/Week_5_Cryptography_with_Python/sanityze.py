text = "IF YOU CAN READ THIS YOU MANAGED TO BREAK THE VIGENERE CIPHER THIS IS AN IMPORTANT FIRST STEP IN THIS BONUS ASSIGNMENT THE ACTUAL BONUS ASSIGNMENT CAN BE FOUND IN THE PDF FILE PROVIDED IN THE DEDICATED SECTION CALLED BONUS ASSIGNMENT ON THE PEARL CRYPTOGRAPHY PAGE ON CANVAS A PASSWORD IS NEEDED TO OPEN THE PDF FILE WE PROVIDE THIS PASSWORD IN ENCRYPTED FORMAT THE END OF THIS MESSAGE DENOTED AS W THE PASSWORD HAS BEEN ENCRYPTED USING THE RSA CRYPTOSYSTEM WITH THE STATED RSA PUBLIC MODULUS N AND PUBLIC EXPONENT E YOUR TASK IS TO WRITE YOUR OWN PYTHON PROGRAM THAT BREAKS THE ENCRYPTION OF THE PASSWORD IN ORDER TO READ THE PDF FILE ALTHOUGH THER S A MODULUS N IS LARGE IT MIGHT MAKE SENSE TO TRY TO FACTORIZE IT TO EASE THIS PROCESS WE WOULD LIKE TO PROVIDE YOU WITH THE BELOW STATED ADDITIONAL RSA MODULI A B C AND D WHICH HAVE BEEN USED IN A COMPLETELY DIFFERENT CONTEXT BUT THAT HAVE BEEN GENERATED WITH THE SAME BAD RANDOM PRIME GENERATOR AS WAS USED TO GENERATE N MAYBE THEY HELP YOU TO FACTORIZE N"
text = text.replace(" ", "")

j = 0

for i in range(len(text)):
    if j % 6 == 0:
        print(" ", end="")
        j = 0
    print(text[i], end="")
    j += 1

print()

