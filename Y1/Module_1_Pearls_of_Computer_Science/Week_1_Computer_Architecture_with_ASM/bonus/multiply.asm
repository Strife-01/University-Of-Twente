.device atmega328p

ldi r17,$4 ; one multiplicand, try other values!
ldi r18,$5 ; the other multiplicand, try other values!

;
ldi r16,$0 ; empty r16 to store the result

loop_untill_r18_is_0:
  sbrc r17,0  ; if the carry from the last right shift of r17 is 0 we skip the addition
  add r16,r18 ; add the current value of r18 (shifted from last step left)
              ; if the right shift of r17 is set
  lsl r18     ; left shift r17
  lsr r17     ; right shift r18
  brne loop_untill_r17_is_0 ; if the r17 after right shift is still not 0
                            ; we go back to the beginning of the loop
;

  call sendr16tolaptop ; send calculation result to laptop

again:

  rjmp again ; finished, go into infinite loop

  .include "rs232link.inc"
