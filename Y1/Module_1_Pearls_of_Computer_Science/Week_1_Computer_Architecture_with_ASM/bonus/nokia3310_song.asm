;*************************************************************
; Music Player for ATmega328p
; Plays the Nokia 3310 Ringtone (Gran Vals)
;*************************************************************
; This melody is based on "Gran Vals" by Francisco Tárrega (1852-1909),
; a classical guitar composition originally written in the late 19th century.
; It became globally famous as the default ringtone for Nokia mobile phones,
; particularly the iconic Nokia 3310 released in 2000.
; 
; The original musical sequence is:
; E5 1/8 D5 1/8 S4 1/4 GS4 1/4 CS5 1/8 B4 1/8 D4 1/4 E4 1/4 B4 1/8 A4 1/8 CS4 1/4 E4 1/4 A4 1/2
;*************************************************************

.device atmega328p
.equ DDRB = 4   ; Data Direction Register address
.equ PORTB = 5  ; Output Port Register address

;*************************************************************
; Macro Definitions
;*************************************************************
.macro LOAD_NOTE_PARAMS
    ; Macro to load note parameters to reduce code repetition
    ldi r24, @0   ; Load note repeat count low byte
    ldi r25, @1   ; Load note repeat count high byte
.endmacro

.macro PLAY_NOTE
    ; Macro to play a note with standard on/off cycles
    call p_on
    ldi r26, @0   ; Load duty cycle low byte
    ldi r27, @1   ; Load duty cycle high byte
    rcall delay_note_on
    
    call p_off
    ldi r26, @0   ; Load off-cycle low byte
    ldi r27, @1   ; Load off-cycle high byte
    rcall delay_note_off
.endmacro

;*************************************************************
; Initialization
;*************************************************************
init:
    ; Configure PORTB for LED and buzzer outputs
    ldi r16, $30  ; Set specific pins as outputs
    out DDRB, r16

;*************************************************************
; Main Program: Song Sequence
;*************************************************************
.macro DEFINE_NOTE
    ; Define note sequence with macro for easier maintenance
    note_@0:
        LOAD_NOTE_PARAMS @1, @2
        play_@0_loop:
            PLAY_NOTE @3, @4
            sbiw r25:r24, 1
            brne play_@0_loop
        ret
.endmacro

; Define all notes in the sequence
DEFINE_NOTE E5,  44, 0, $6C, $18
DEFINE_NOTE D5,  44, 0, $3D, $1A
DEFINE_NOTE FS4, 49, 0, $76, $2A
DEFINE_NOTE GS4, 55, 0, $4D, $25
DEFINE_NOTE CS5, 37, 0, $68, $1C
DEFINE_NOTE B4,  33, 0, $42, $1F
DEFINE_NOTE D4,  38, 0, $4B, $35
DEFINE_NOTE E4,  44, 0, $B2, $2F
DEFINE_NOTE A4,  28, 0, $06, $23
DEFINE_NOTE CS4, 37, 0, $D1, $38
DEFINE_NOTE A4_final, 117, 0, $06, $23

;*************************************************************
; Main Execution Loop
;*************************************************************
start:
    ; Initialize the song sequence
    rcall init

    ; Play full song sequence
    rcall note_E5
    rcall note_D5
    rcall note_FS4
    rcall note_GS4
    rcall note_CS5
    rcall note_B4
    rcall note_D4
    rcall note_E4
    rcall note_B4
    rcall note_A4
    rcall note_CS4
    rcall note_E4
    rcall note_A4_final

    ; Repeat song indefinitely
    rjmp start

;*************************************************************
; Subroutines
;*************************************************************
delay_note_on:
    ; Delay subroutine for note on cycle
    sbiw r27:r26, 1
    brne delay_note_on
    ret

delay_note_off:
    ; Delay subroutine for note off cycle
    sbiw r27:r26, 1
    brne delay_note_off
    ret

;*************************************************************
; Utility Functions
;*************************************************************
p_on:
    ; Turn on buzzer and LED
    ldi r16, $30
    out PORTB, r16
    ret

p_off:
    ; Turn off buzzer and LED
    ldi r16, $00
    out PORTB, r16
    ret
