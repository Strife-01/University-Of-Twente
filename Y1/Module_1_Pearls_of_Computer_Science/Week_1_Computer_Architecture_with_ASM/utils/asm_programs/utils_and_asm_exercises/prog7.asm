e300 ; ldi r16,$30 - it loads immediately (byte 0) (not from memory)
     ; the 3(byte 1) 0(byte 3) into register 16(byte 2)

b904 ; out 4,r16 - it takes the data from r16 10000 with command 10111 into DDRB
     ; to make it output pin of the led L 000100

e200 ; ldi r16,00100000 = $20 - it loads directly the value $20 in the register r16
     ; located at 0x00

b905 ; out 5,r16 - write output value 000101 into portB pin that we made as output pin from
     ; the register r16 10000

cfff ; rjmp -1 - make a relative jump, from where we currenlty are to -1 + 1 = 0 so it will
     ; repeat the same cfff again - 2nd complement
