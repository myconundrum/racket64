#lang racket 
(require threading racket/format)

; 6502 default memory locations
(define stack-base #x0100)
(define reset-vector #xfffc) ; On reset, the PC register is loaded with the value of this address.
(define nmi-vector #xfffa)  ; non-maskable interrupt routine stored in this address.
(define irq-vector #xfffe)  ; interrupt request routine stored in this address.

;; ------------------------------------6502 instruction data ------------------------------------------
; intermediate tables are all used to build up final "opcodes" vector
; this table hashes all opcodes of a given addressing mode.
(define op-by-mode-hash 
  (hash
   'immediate (list #x69 #x29 #xc9 #xe0 #xc0 #x49 #xa9 #xa2 #xa0 #x09 #xe9)
   'zero-page (list #x65 #x25 #x06 #x24 #xc5 #xe4 #xc4 #xc6 #x45 #xe6 #xa5 #xa6 #xa4 #x46 #x05 #x26 
                    #x66 #xe5 #x85 #x86 #x84)
   'zero-page-x (list #x75 #x35 #x16 #xd5 #xd6 #x55 #xf6 #xb5 #xb4 #x56 #x15 #x36 #x76 #xf5 #x95 #x94)
   'zero-page-y (list #xb6 #x96)
   'absolute (list #x6d #x2d #x0e #x2c #xcd #xec #xcc #xce #x4d #xee #x4c #x20 #xad #xae #xac #x4e #x0d
                   #x2e #x6e #xed #x8d #x8e #x8c)
   'absolute-x (list #x7d #x3d #x1e #xdd #xde #x5d #xfe #xbd #xbc #x5e #x1d #x3e #x7e #xfd #x9d)
   'absolute-y (list #x79 #x39  #xd9 #x59 #xb9 #xbe #x19 #xf9 #x99)
   'indirect (list #x6c)
   'indexed-indirect (list #x61 #x21 #xc1 #x41 #xa1 #x01 #xe1 #x81)
   'indirect-indexed (list #x71 #x31 #xd1 #x51 #xb1 #x11 #xf1 #x91)
   'implied (list #x4a #x0a #x2a #x6a #x00 #x18 #xd8 #x58 #xb8 #xca #x88 #xe8 #xc8 #xea #x48 #x08
                  #x68 #x28 #x40 #x60 #x38 #xf8 #x78 #xaa #xa8 #xba #x8a #x9a #x98)
   'relative (list #x90 #xb0 #xf0 #x30 #xd0 #x10 #x50 #x70)))

(define (add-ops-to-hash h v l) (if (null? l) h (add-ops-to-hash (hash-set h (first l) v) v (rest l))))
(define mode-by-op-hash
  (for/fold ([rhash (hash)]) ([key (hash-keys op-by-mode-hash)])
    (add-ops-to-hash rhash key (hash-ref op-by-mode-hash key))))

; this table matches the specific function to set address lines for an address mode.
(define address-mode-functions 
  (hash 
   'implied (λ (cpu) cpu)
   'immediate (λ (cpu) (inc-pc (poke cpu '_data (peek cpu 'pc))))
   'zero-page (λ (cpu) (inc-pc (poke cpu '_data (peek cpu (peek cpu 'pc))))) 
   'zero-page-x (λ (cpu) (inc-pc (poke cpu '_data (byte-add (peek cpu (peek cpu 'pc)) (peek cpu 'x)))))
   'zero-page-y (λ (cpu)  (inc-pc (poke cpu '_data (byte-add (peek cpu (peek cpu 'pc)) (peek cpu 'y)))))
   'absolute (λ (cpu) (inc-pc-2  (poke cpu '_data (peek-word cpu (peek cpu 'pc)))))
   'absolute-x (λ (cpu) (inc-pc-2 (poke cpu '_data (word-add (peek-word cpu (peek cpu 'pc)) (peek cpu 'x)))))
   'absolute-y (λ (cpu) (inc-pc-2 (poke cpu '_data (word-add (peek-word cpu (peek cpu 'pc)) (peek cpu 'y)))))
   'indirect (λ (cpu) (inc-pc-2 (poke cpu '_data (peek-word cpu (peek-word cpu (peek cpu 'pc))))))
   'indexed-indirect 
   (λ (cpu) (inc-pc (poke cpu '_data (peek-word cpu (byte-add (peek cpu (peek cpu 'pc) (peek cpu 'x)))))))
   'indirect-indexed 
   (λ (cpu) (inc-pc (poke cpu '_data (word-add (peek-word cpu (peek cpu (peek cpu 'pc))) (peek cpu 'x)))))
   'relative (λ (cpu) (inc-pc (poke cpu '_data (peek cpu 'pc))))))

; this table contains the base name, function, and associated opcodes.
(struct base (name opcodes fn))
(define base-opcode-list 
  (list 
   (base "LDA" '(#xa9 #xa5 #xb5 #xad #xbd #xb9 #xa1 #xb1) 
         (λ (cpu) (flag-set-nz (poke cpu 'a (peek-data cpu)) 'a)))
   (base "LDY" '(#xa0 #xa4 #xb4 #xac #xbc) (λ (cpu) (flag-set-nz (poke cpu 'y (peek-data cpu)) 'y)))
   (base "LDX" '(#xa2 #xa6 #xb6 #xae #xbe) (λ (cpu) (flag-set-nz (poke cpu 'x (peek-data cpu)) 'x)))
   (base "STA" '(#x85 #x95 #x8d #x9d #x99 #x81 #x91)
         (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'a)) 'a)))
   (base "STX" '(#x86 #x96 #x8e) (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'x))'x)))
   (base "STY" '(#x84 #x94 #x8c) (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'y))'y)))
   (base "TAX" '(#xaa) (λ (cpu) (flag-set-nz  (poke cpu 'x (peek cpu 'a)) 'x)))
   (base "TAY" '(#xa8) (λ (cpu) (flag-set-nz  (poke cpu 'y (peek cpu 'a)) 'y)))
   (base "TSX" '(#xba) (λ (cpu) (flag-set-nz  (poke cpu 'x (peek cpu 'sp)) 'x)))
   (base "TXA" '(#x8a) (λ (cpu) (flag-set-nz  (poke cpu 'a (peek cpu 'x)) 'a)))
   (base "TYA" '(#x98) (λ (cpu) (flag-set-nz  (poke cpu 'a (peek cpu 'y)) 'a)))
   (base "TXS" '(#x9a) (λ (cpu) (flag-set-nz  (poke cpu 'sp (peek cpu 'x)) 'sp)))
   (base "JMP" '(#x4c #x6c) (λ (cpu) (poke cpu 'pc (peek-data-address cpu)) ))
   (base "PHP" '(#x08) (λ (cpu) (push cpu (peek cpu 'ps))))
   (base "PHA" '(#x48) (λ (cpu) (push cpu (peek cpu'a))))
   (base "PLP" '(#x28) (λ (cpu) (pull cpu 'ps)))
   (base "PLA" '(#x68) (λ (cpu) (flag-set-nz (pull cpu 'a))))
   (base "CLV" '(#xb8) (λ (cpu) (flag-clear cpu 'v)))
   (base "CLI" '(#x58) (λ (cpu) (flag-clear cpu 'i)))
   (base "CLD" '(#xd8) (λ (cpu) (flag-clear cpu 'd)))
   (base "CLC" '(#x18) (λ (cpu) (flag-clear cpu 'c)))
   (base "SEI" '(#x78) (λ (cpu) (flag-set cpu 'i)))
   (base "SED" '(#xf8) (λ (cpu) (flag-set cpu 'd)))
   (base "SEC" '(#x38) (λ (cpu) (flag-set cpu 'c)))
   (base "INX" '(#xe8) (λ (cpu) (flag-set-nz (inc cpu 'x) 'x)))
   (base "INY" '(#xc8) (λ (cpu) (flag-set-nz (inc cpu 'y) 'y)))
   (base "DEX" '(#xca) (λ (cpu) (flag-set-nz (dec cpu 'x) 'x)))
   (base "DEY" '(#x88) (λ (cpu) (flag-set-nz (dec cpu 'y) 'y)))
   (base "INC" '(#xe6 #xf6 #xee #xfe) 
         (λ (cpu) (flag-set-nz (inc cpu (peek-data-address cpu)) (peek-data-address cpu))))
   (base "DEC" '(#xc6 #xd6 #xce #xde) 
         (λ (cpu) (flag-set-nz (dec cpu (peek-data-address cpu)) (peek-data-address cpu))))
   (base "AND" '(#x29 #x25 #x35 #x2d #x3d #x39 #x21 #x31)
         (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-and (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "ORA" '(#x09 #x05 #x15 #x0d #x1d #x19 #x01 #x11)
          (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-ior (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "EOR" '(#x49 #x45 #x55 #x4d #x5d #x59 #x41 #x51)
         (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-xor (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "BIT" '(#x24 #x2c) 
         (λ (cpu) (define val (bitwise-and (peek cpu 'a) (peek-data cpu))) 
            (~> (flag-if-zero cpu val) (flag-if-has-flag 'v val) (flag-if-has-flag 'n val))))
   (base "BCC" '(#x90) (λ (cpu) (if (flag-clear? cpu 'c) (make-relative-jump cpu) cpu)))
   (base "BCS" '(#xb0) (λ (cpu) (if (flag-set? cpu 'c) (make-relative-jump cpu) cpu)))
   (base "BEQ" '(#xf0) (λ (cpu) (if (flag-set? cpu 'z) (make-relative-jump cpu) cpu)))
   (base "BNE" '(#xd0) (λ (cpu) (if (flag-clear? cpu 'z) (make-relative-jump cpu) cpu)))
   (base "BMI" '(#x30) (λ (cpu) (if (flag-set? cpu 'n) (make-relative-jump cpu) cpu)))
   (base "BPL" '(#x10) (λ (cpu) (if (flag-clear? cpu 'n) (make-relative-jump cpu) cpu)))
   (base "BVC" '(#x50) (λ (cpu) (if (flag-clear? cpu 'v) (make-relative-jump cpu) cpu)))
   (base "BVS" '(#x70) (λ (cpu) (if (flag-set? cpu 'v) (make-relative-jump cpu) cpu)))
   (base "JSR" '(#x20) (λ (cpu) (poke (push-word cpu (- (peek cpu 'pc) 1)) 'pc (peek-data-address cpu)))) 
   (base "RTS" '(#x60) (λ (cpu) (inc-pc (pull-word cpu 'pc))))))

(define (get-base v bases)
  (cond 
    [(null? bases) (base "UIM" (list v) (λ (cpu) cpu))]
    [(member v (base-opcodes (first bases))) (first bases)]
    [else (get-base v (rest bases))]))

(struct opcode (name op mode modefn fn) #:transparent)
(define (make-op v)
  (define b (get-base v base-opcode-list))
  (define mode (hash-ref mode-by-op-hash v 'immediate))
  (opcode (base-name b) v mode (hash-ref address-mode-functions mode) (base-fn b)))

; finaly can build the complete opcodes list. 
(define opcodes (build-vector #xff make-op))
;; -----------------------------------End of 6502 instruction data.

(define (init-memory cpu)
  (~> (poke cpu reset-vector 0) (poke (add1 reset-vector) #xe0)
   (load-bytes #xe000 '(#xa2 #xff #x9a #xa2 0 #x4c 0 0)))) 
   ; very simple ROM. LDX #$FF TXS LDX #$00 JMP $0000 (set stack pointer, clear flags)

; create and initialize a 6502 cpu.
(define (make-cpu) 
  (define cpu (init-memory (hash)))  ; extremely simplistic data structure, just a hash.
  ; initialize cpu state.
  (~> (poke cpu 'pc (peek-word cpu reset-vector)) ; load the pc from the value loaded in the reset vector.
      (flag-set 'u))) ; unused flag. Should be tied to logical one always.


; utility functions
(define (twos-complement val) (* (+ (bitwise-and (bitwise-not val) #xff) 1) -1))
(define (byte-add a b) (define ab (+ a b)) (if (> ab #xff) (- ab #xff) ab))
(define (word-add a b) (define ab (+ a b)) (if (> ab #xffff) (- ab #xffff) ab))
;
; BUGBUG Not yet implimented
;
(define (byte-sub a b) (define ab (- a b)) (if (< 0 ab) (abs ab) ab))
(define (word-sub a b) (define ab (- a b)) (if (< 0 ab) (abs ab) ab))

; basic cpu manipulation functions
(define (peek cpu addr) (hash-ref cpu addr 0))
(define (poke cpu addr val) (hash-set cpu addr val))
(define (inc cpu addr) (poke cpu addr (byte-add (peek cpu addr) 1)))
(define (dec cpu addr) (poke cpu addr (byte-sub (peek cpu addr) 1)))
(define (inc-word cpu addr) (poke cpu addr (word-add (peek cpu addr) 1)))
(define (dec-word cpu addr) (poke cpu addr (word-sub (peek cpu addr) 1)))
(define (peek-word cpu addr)
  (bitwise-ior (bitwise-and (peek cpu addr) #xff) 
               (arithmetic-shift  (bitwise-and (peek cpu (add1 addr)) #xff) 8)))

; accelerators 
(define (peek-data-address cpu) (peek cpu '_data))
(define (peek-data cpu) (peek cpu (peek cpu '_data)))
(define (inc-pc cpu) (inc-word cpu 'pc))
(define (inc-pc-2 cpu) (poke cpu 'pc (word-add (peek cpu 'pc) 2)))
(define (make-relative-jump cpu) 
  (define v (peek-data cpu)) 
  (poke cpu 'pc (+ (peek cpu 'pc) 
                   (if (> (bitwise-and v (flag 'n)) 0) (twos-complement v) v))))

; stack operations
(define (push cpu val) (~> (poke cpu (+ stack-base (peek cpu 'sp)) val) (dec 'sp)))
(define (pull cpu reg) (~> (inc cpu 'sp) (poke reg (peek cpu (+ stack-base (add1 (peek cpu 'sp)))))))
(define (push-word cpu val) 
  (~> (push cpu (bitwise-and (arithmetic-shift val -8) #xff)) (push (bitwise-and val #xff))))
(define (pull-word cpu reg) 
  (define lo-cpu (pull cpu reg))
  (define hi-cpu (pull lo-cpu reg))
  (poke hi-cpu reg (bitwise-ior (arithmetic-shift (peek hi-cpu reg) 8) (peek lo-cpu reg))))

; flag manipulation routines for the processor status register.
(define flags (hash 'c #x01 'z #x02 'i #x04 'd #x08 'b #x10 'u #x20 'v #x40 'n #x80))
(define (flag f) (hash-ref flags f))
(define (flag-set? cpu f) (> (bitwise-and (peek cpu 'ps) (flag f))0))
(define (flag-clear? cpu f) (not (flag-set? cpu f)))
(define (flag-set cpu f) (poke cpu 'ps (bitwise-ior (flag f) (peek cpu 'ps))))
(define (flag-clear cpu f) (poke cpu 'ps (bitwise-and (peek cpu 'ps) (bitwise-not (flag f)))))
(define (flag-if-zero cpu f val) (if (= 0 val) (flag-set cpu f) (flag-clear cpu f)))
(define (flag-if-not-zero cpu f val) (if (not (= 0 val)) (flag-set cpu f) (flag-clear cpu f)))
(define (flag-if-has-flag cpu f val) (flag-if-not-zero cpu f (bitwise-and (flag f) val)))
(define (flag-set-nz cpu addr) 
  (define val (peek cpu addr)) (~> (flag-if-zero cpu 'z val) (flag-if-has-flag 'n val)))


(define (hex-string num width) (~a (format "~x" num) #:align 'right #:width width #:pad-string "0"))
(define (bin-string num width) (~a (format "~b" num) #:align 'right #:width width #:pad-string "0"))
(define (display-cpu cpu op)
  (printf "|NVUBDIZC| ~a\n|~a| a: $~a x: $~a y: $~a sp: $~a pc: $~a\n"
          (opcode-name op) (bin-string (peek cpu 'ps) 8)
          (hex-string (peek cpu 'a) 2) (hex-string (peek cpu 'x) 2) (hex-string (peek cpu 'y) 2)
          (hex-string (peek cpu 'sp) 2) (hex-string (peek cpu 'pc) 4) ) cpu)

(define (load-bytes cpu address bs)
  (if (null? bs) cpu (load-bytes (poke cpu address (first bs)) (add1 address) (rest bs))))

(define (exec cpu)
  (define op (vector-ref opcodes (peek cpu (peek cpu 'pc))))
  (if (string=? (opcode-name op) "UIM") cpu
      (exec (~> (inc-pc cpu)           ; fetch opcode.
                ((opcode-modefn op) _) ; decode address and set address lines.
                ((opcode-fn op) _)     ; execute instruction
                (display-cpu op)))))


(define (test-prog cpu)

  (~> 
   (load-bytes cpu 0 
               '(#xa2 10          ; LDX #10
                 #x8a             ; LOOP: TXA
                 #x20 #x00 #x10   ; JSR $1000
                 #xca             ; DEX
                 #xd0 #xf9        ; BNE LOOP
                 ))
   (load-bytes #x1000 
               '(#x95 #xa0   ; STA $A0, X 
                 #x60        ; RTS
                 ))


))
