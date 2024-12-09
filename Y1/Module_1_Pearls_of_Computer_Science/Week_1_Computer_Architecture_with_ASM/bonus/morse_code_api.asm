.device atmega328p ; what type of processor do we use? do NOT change!

.equ DDRB = 4   ; address of data direction register; do NOT change!
.equ PORTB = 5  ; address of output port register; do NOT change!
.equ FINISH_LOOP = 0 ; def

prescaler_slow_down_setup:
  ldi r31, $00
  ldi r30, $61      ; target clkpr
  ldi r16, $80      ; store on bit
  st Z, r16
  ldi r16, $08      ; set to 1/256 prescaler
  st Z, r16

setup_output_direction_port_b:
  ldi r16,$20   ; register 16 now contains 0010 0000
  out DDRB,r16  ; write this to the data direction register to make
                ; the LED and buzzer pins act as outputs

start:
  call letter_A
  call space_between_letters
  call letter_B
  call space_between_words

again:          ; this is not an instruction, but a label, as
                ; indicated by the colon at the end
  rjmp start    ; infinite loop: jump back to the label




; LETTERS

letter_A:
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_B:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_C:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_D:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_E:
  call dot
  ret

letter_F:
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_G:
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_H:
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_I:
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_J:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  ret

letter_K:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_L:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_M:
  call dash
  call space_between_parts_of_same_letter
  call dash
  ret

letter_N:
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_O:
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  ret

letter_P:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_Q:
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_R:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  ret

letter_S:
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

letter_T:
  call dash
  ret

letter_U:
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_V:
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_W:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  ret

letter_X:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  ret

letter_Y:
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dash
  ret

letter_Z:
  call dash
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter
  call dot
  call space_between_parts_of_same_letter
  call dot
  ret

digit_0:
  call dot
  call space_between_parts_of_same_letter
  call dash
  call space_between_parts_of_same_letter


; UTILS

power_on_led:
  ldi r16,$20   ; register 16 now contains 0010 0000
  out PORTB,r16 ; write to the output port itself, which switches
                ; the LED on
  ret

power_off_led:
  ldi r16,$00   ; register 16 now contains 0000 0000
  out PORTB,r16 ; write to the output port itself, which switches
                ; the LED off
  ret

dot:                                  ; length 1 unit
  call power_on_led
  call pause_one_unit
  call power_off_led
  ret

dash:                                 ; length 3 units
  call power_on_led
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  call power_off_led
  ret

space_between_parts_of_same_letter:   ; length 1 unit
  call pause_one_unit
  ret

space_between_letters:                ; length 3 units
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  ret

space_between_words:                  ; length 7 units
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  call pause_one_unit
  ret

pause_one_unit:                       ; length 1 unit
  call config_time
  call repeat
  ret

repeat:                               ; subtract 1 untill 0 then go back
  sbiw r25:r24,1
  brne repeat
  ret

config_time:    ; creating decrementing subroutine decrements - 1 unit of time
  ldi r25,$0f   ; load the 15 val in r25 for utilizing it as MSB for subtraction
  ldi r24,$ff   ; load the 255 val in r24 for utilizing it as LSB for subtraction
  ret


; comands
; sbiw subtract immediate from word sbiw r1:r0,subtract
; breq branch if equal breq num
