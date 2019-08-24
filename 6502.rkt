#lang racket

(require threading racket/format)

(provide 
 add-mem-map
 remove-mem-map
 make-cpu
 init-cpu
 peek
 poke
 exec
 step
 peek-word
 register-string
 disassemble
 disassemble-lines
 flag-set?
)

; 6502 default memory locations
(define stack-base #x0100)
(define reset-vector #xfffc) ; On reset, the PC register is loaded with the value of this address.
(define nmi-vector #xfffa)  ; non-maskable interrupt routine stored in this address.
(define irq-vector #xfffe)  ; interrupt request routine stored in this address.

;; ------------------------------------6502 instruction data ------------------------------------------
; intermediate tables are all used to build up final "opcodes" vector

; base cycle-counts by instruction. Does not count page boundaries and other conditions.
(define cycle-counts 
  (hash
   #x69 2 #x65 3 #x75 4 #x6d 4 #x7d 4 #x79 4 #x61 6 #x71 5 #x29 2 #x25 3 #x35 4 #x2d 4
   #x3d 4 #x39 4 #x21 6 #x31 5 #x0a 2 #x06 5 #x16 6 #x0e 6 #x1e 7 #x90 2 #xb0 2 #xf0 2
   #x24 3 #x2c 4 #x30 2 #xd0 2 #x10 2 #x00 7 #x50 2 #x70 2 #x18 2 #xd8 2 #x58 2 #xb8 2 
   #xc9 2 #xc5 3 #xd5 4 #xcd 4 #xdd 4 #xd9 4 #xc1 6 #xd1 5 #xe0 2 #xe4 3 #xec 4 #xc0 2
   #xc4 3 #xcc 4 #xc6 5 #xd6 6 #xce 6 #xde 7 #xca 2 #x88 2 #x49 2 #x45 3 #x55 4 #x4d 4
   #x5d 4 #x59 4 #x41 6 #x51 5 #xe6 5 #xf6 6 #xee 6 #xfe 7 #xe8 2 #xc8 2 #x4c 3 #x6c 5
   #x20 6 #xa9 2 #xa5 3 #xb5 4 #xad 4 #xbd 4 #xb9 4 #xa1 6 #xb1 5 #xa2 2 #xa6 3 #xb6 4
   #xae 4 #xbe 4 #xa0 2 #xa4 3 #xb4 4 #xac 4 #xbc 4 #x4a 2 #x46 5 #x56 6 #x4e 6 #x5e 7
   #xea 2 #x09 2 #x05 3 #x15 4 #x0d 4 #x1d 4 #x19 4 #x01 6 #x11 5 #x48 3 #x08 3 #x68 4
   #x28 4 #x2a 2 #x26 5 #x36 6 #x2e 6 #x3e 7 #x6a 2 #x66 5 #x76 6 #x6e 6 #x7e 7 #x40 6
   #x60 6 #xe9 2 #xe5 3 #xf5 4 #xed 4 #xfd 4 #xf9 4 #xe1 6 #xf1 5 #x38 2 #xf8 2 #x78 2
   #x85 3 #x95 4 #x8d 4 #x9d 5 #x99 5 #x81 6 #x91 6 #x86 3 #x96 4 #x8e 4 #x84 3 #x94 4
   #x8c 4 #xaa 2 #xa8 2 #xba 2 #x8a 2 #x9a 2 #x98 2))

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
   'indirect (λ (cpu) (inc-pc-2 (poke cpu '_data  (peek-word cpu (peek cpu 'pc)))))
   'indexed-indirect 
   (λ (cpu) (inc-pc (poke cpu '_data (peek-word cpu (byte-add (peek cpu (peek cpu 'pc) (peek cpu 'x)))))))
   'indirect-indexed 
   (λ (cpu) (inc-pc (poke cpu '_data (word-add (peek-word cpu (peek cpu (peek cpu 'pc))) (peek cpu 'x)))))
   'relative (λ (cpu) (inc-pc (poke cpu '_data (peek cpu 'pc))))))


(define mode-disassemble 
  (hash 
   'implied (λ (cpu op) (format "~a       :~a" (hex-string (opcode-op op) 2) (opcode-name op)))
   'immediate (λ (cpu op) 
                (format "~a ~a    :~a  #$~a" (hex-string (opcode-op op) 2) (hex-string (peek-data cpu) 2) 
                        (opcode-name op) (hex-string (peek-data cpu) 2)))
   'zero-page (λ (cpu op)  (format "~a ~a   :~a  $~a" (hex-string (opcode-op op) 2) 
                                (hex-string (peek-data-address cpu) 2) (opcode-name op)
                                (hex-string (peek-data-address cpu) 2)))
   'zero-page-x (λ (cpu op)  (format "~a ~a   :~a  $~a,x" (hex-string (opcode-op op) 2) 
                                (hex-string (peek-data-address cpu) 2) (opcode-name op)
                                (hex-string (peek-data-address cpu) 2)))
   'zero-page-y (λ (cpu op)  (format "~a ~a   :~a  $~a,y" (hex-string (opcode-op op) 2) 
                                (hex-string (peek-data-address cpu) 2) (opcode-name op)
                                (hex-string (peek-data-address cpu) 2))) 
   'absolute (λ (cpu op) (format "~a ~a ~a :~a $~a"
                                 (hex-string (opcode-op op) 2) 
                                 (hex-string (bitwise-and (peek-data-address cpu) #xff) 2)
                                 (hex-string (arithmetic-shift (peek-data-address cpu) -8) 2)
                                 (opcode-name op) (hex-string (peek-data-address cpu) 4)))
   'absolute-x (λ (cpu op) (format "~a ~a ~a :~a $~a,x"
                                   (hex-string (opcode-op op) 2) 
                                   (hex-string (bitwise-and (peek-data-address cpu) #xff) 2)
                                   (hex-string (arithmetic-shift (peek-data-address cpu) -8) 2)
                                   (opcode-name op) (hex-string (peek-data-address cpu) 4)))
   'absolute-y (λ (cpu op) (format "~a ~a ~a :~a $~a,y"
                                   (hex-string (opcode-op op) 2) 
                                   (hex-string (bitwise-and (peek-data-address cpu) #xff) 2)
                                   (hex-string (arithmetic-shift (peek-data-address cpu) -8) 2)
                                   (opcode-name op) (hex-string (peek-data-address cpu) 4)))
   'indirect (λ (cpu op) (format "~a ~a ~a :~a ($~a)"
                                 (hex-string (opcode-op op) 2) 
                                 (hex-string (bitwise-and (peek-data-address cpu) #xff) 2)
                                 (hex-string (arithmetic-shift (peek-data-address cpu) -8) 2)
                                 (opcode-name op) (hex-string (peek-data-address cpu) 4)))
   'indexed-indirect (λ (cpu op)  (format "~a ~a   :~a  ($~a,x)" (hex-string (opcode-op op) 2) 
                                (hex-string (peek-data-address cpu) 2) (opcode-name op)
                                (hex-string (peek-data-address cpu) 2)))
   'indirect-indexed (λ (cpu op)  (format "~a ~a   :~a  ($~a),y" (hex-string (opcode-op op) 2) 
                                (hex-string (peek-data-address cpu) 2) (opcode-name op)
                                (hex-string (peek-data-address cpu) 2)))
   'relative (λ (cpu op) 
                (format "~a ~a    :~a  $~a" (hex-string (opcode-op op) 2) (hex-string (peek-data cpu) 2) 
                        (opcode-name op) (hex-string (peek-data cpu) 2)))))




; this table contains the base name, function, and associated opcodes.
(struct base (name opcodes fn))
(define base-opcode-list 
  (list 
   (base "lda" '(#xa9 #xa5 #xb5 #xad #xbd #xb9 #xa1 #xb1) 
         (λ (cpu) (flag-set-nz (poke cpu 'a (peek-data cpu)) 'a)))
   (base "ldy" '(#xa0 #xa4 #xb4 #xac #xbc) (λ (cpu) (flag-set-nz (poke cpu 'y (peek-data cpu)) 'y)))
   (base "ldx" '(#xa2 #xa6 #xb6 #xae #xbe) (λ (cpu) (flag-set-nz (poke cpu 'x (peek-data cpu)) 'x)))
   (base "sta" '(#x85 #x95 #x8d #x9d #x99 #x81 #x91)
         (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'a)) 'a)))
   (base "stx" '(#x86 #x96 #x8e) (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'x))'x)))
   (base "sty" '(#x84 #x94 #x8c) (λ (cpu) (flag-set-nz (poke cpu (peek-data-address cpu) (peek cpu 'y))'y)))
   (base "tax" '(#xaa) (λ (cpu) (flag-set-nz  (poke cpu 'x (peek cpu 'a)) 'x)))
   (base "tay" '(#xa8) (λ (cpu) (flag-set-nz  (poke cpu 'y (peek cpu 'a)) 'y)))
   (base "tsx" '(#xba) (λ (cpu) (flag-set-nz  (poke cpu 'x (peek cpu 'sp)) 'x)))
   (base "txa" '(#x8a) (λ (cpu) (flag-set-nz  (poke cpu 'a (peek cpu 'x)) 'a)))
   (base "tya" '(#x98) (λ (cpu) (flag-set-nz  (poke cpu 'a (peek cpu 'y)) 'a)))
   (base "txs" '(#x9a) (λ (cpu) (flag-set-nz  (poke cpu 'sp (peek cpu 'x)) 'sp)))
   (base "jmp" '(#x4c) (λ (cpu) (poke cpu 'pc (peek-data-address cpu)) ))
   (base "jmp" '(#x6c) (λ (cpu) (poke cpu 'pc (peek-data cpu)) ))
   (base "php" '(#x08) (λ (cpu) (push cpu (peek cpu 'ps))))
   (base "pha" '(#x48) (λ (cpu) (push cpu (peek cpu'a))))
   (base "plp" '(#x28) (λ (cpu) (pull cpu 'ps)))
   (base "pla" '(#x68) (λ (cpu) (flag-set-nz (pull cpu 'a))))
   (base "clv" '(#xb8) (λ (cpu) (flag-clear cpu 'v)))
   (base "cli" '(#x58) (λ (cpu) (flag-clear cpu 'i)))
   (base "cld" '(#xd8) (λ (cpu) (flag-clear cpu 'd)))
   (base "clc" '(#x18) (λ (cpu) (flag-clear cpu 'c)))
   (base "sei" '(#x78) (λ (cpu) (flag-set cpu 'i)))
   (base "sed" '(#xf8) (λ (cpu) (flag-set cpu 'd)))
   (base "sec" '(#x38) (λ (cpu) (flag-set cpu 'c)))
   (base "inx" '(#xe8) (λ (cpu) (flag-set-nz (inc cpu 'x) 'x)))
   (base "iny" '(#xc8) (λ (cpu) (flag-set-nz (inc cpu 'y) 'y)))
   (base "dex" '(#xca) (λ (cpu) (flag-set-nz (dec cpu 'x) 'x)))
   (base "dey" '(#x88) (λ (cpu) (flag-set-nz (dec cpu 'y) 'y)))
   (base "inc" '(#xe6 #xf6 #xee #xfe) 
         (λ (cpu) (flag-set-nz (inc cpu (peek-data-address cpu)) (peek-data-address cpu))))
   (base "dec" '(#xc6 #xd6 #xce #xde) 
         (λ (cpu) (flag-set-nz (dec cpu (peek-data-address cpu)) (peek-data-address cpu))))
   (base "and" '(#x29 #x25 #x35 #x2d #x3d #x39 #x21 #x31)
         (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-and (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "ora" '(#x09 #x05 #x15 #x0d #x1d #x19 #x01 #x11)
          (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-ior (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "eor" '(#x49 #x45 #x55 #x4d #x5d #x59 #x41 #x51)
         (λ (cpu) (flag-set-nz (poke cpu 'a (bitwise-xor (peek cpu 'a) (peek-data cpu))) 'a)))
   (base "bit" '(#x24 #x2c) 
         (λ (cpu) (define val (bitwise-and (peek cpu 'a) (peek-data cpu))) 
            (~> (flag-if-zero cpu val) (flag-if-has-flag 'v val) (flag-if-has-flag 'n val))))
   (base "bcc" '(#x90) (λ (cpu) (if (flag-clear? cpu 'c) (make-relative-jump cpu) cpu)))
   (base "bcs" '(#xb0) (λ (cpu) (if (flag-set? cpu 'c) (make-relative-jump cpu) cpu)))
   (base "beq" '(#xf0) (λ (cpu) (if (flag-set? cpu 'z) (make-relative-jump cpu) cpu)))
   (base "bne" '(#xd0) (λ (cpu) (if (flag-clear? cpu 'z) (make-relative-jump cpu) cpu)))
   (base "bmi" '(#x30) (λ (cpu) (if (flag-set? cpu 'n) (make-relative-jump cpu) cpu)))
   (base "bpl" '(#x10) (λ (cpu) (if (flag-clear? cpu 'n) (make-relative-jump cpu) cpu)))
   (base "bvc" '(#x50) (λ (cpu) (if (flag-clear? cpu 'v) (make-relative-jump cpu) cpu)))
   (base "bvs" '(#x70) (λ (cpu) (if (flag-set? cpu 'v) (make-relative-jump cpu) cpu)))
   (base "jsr" '(#x20) (λ (cpu) (poke (push-word cpu (- (peek cpu 'pc) 1)) 'pc (peek-data-address cpu)))) 
   (base "rts" '(#x60) (λ (cpu) (inc-pc (pull-word cpu 'pc))))
   (base "asl" '(#x0a) (λ (cpu) (op-logical-shifter cpu 'a #x80 1)))
   (base "asl" '(#x06 #x16 #x0e #x1e) (λ (cpu) (op-logical-shifter cpu (peek-data-address cpu) #x80 1)))
   (base "lsr" '(#x4a) (λ (cpu) (op-logical-shifter cpu 'a #x01 -1)))
   (base "lsr" '(#x46 #x56 #x4e #x5e) (λ (cpu) (op-logical-shifter cpu (peek-data-address cpu) #x01 -1)))
   (base "rol" '(#x2a) (λ (cpu) (op-rotating-shifter cpu 'a #x80 1)))
   (base "rol" '(#x26 #x36 #x2e #x3e) (λ (cpu) (op-rotating-shifter cpu (peek-data-address cpu) #x80 1)))
   (base "ror" '(#x6a) (λ (cpu) (op-rotating-shifter cpu 'a #x01 -1)))
   (base "ror" '(#x66 #x76 #x6e #x7e) (λ (cpu) (op-rotating-shifter cpu (peek-data-address cpu) #x01 -1)))
   (base "nop" '(#xea) (λ (cpu) cpu))
   (base "cmp" '(#xc9 #xc5 #xd5 #xcd #xdd #xd9 #xc1 #xd1) (λ (cpu) (op-comparator cpu 'a)))
   (base "cpx" '(#xe0 #xe4 #xec) (λ (cpu) (op-comparator cpu 'x)))
   (base "cpy" '(#xc0 #xc4 #xcc) (λ (cpu) (op-comparator cpu 'y)))))

(define (op-logical-shifter cpu addr bit dir)
  (define c2 (~> (carry-if-bit cpu (peek cpu addr) bit)
                 (poke addr (bitwise-and (arithmetic-shift (peek cpu addr) dir) #xff))))
  (flag-set-nz c2 (peek c2 addr)))

(define (op-rotating-shifter cpu addr bit dir)
  (define setcarry ((bitwise-and bit (peek cpu addr)) 0))
  (define c2 (~> (poke cpu (bitwise-and (arithmetic-shift (peek cpu addr) dir) #xff))
                 (rot-carry-bit addr (if (= bit #x80) #x01 #x80))))
  (define c3 (flag-set-nz c2 addr))
  (if setcarry (flag-set c3 'c) (flag-clear c3 'c)))

(define (op-comparator cpu reg)
  (define v (- (peek cpu reg) (peek-data cpu))) 
  (~> (flag-if cpu 'z (= v 0)) (flag-if 'c (>= v 0)) (flag-if-has-flag 'n v)))

(define (get-base v bases)
  (cond 
    [(null? bases) (base "hcf" (list v) (λ (cpu) cpu))]
    [(member v (base-opcodes (first bases))) (first bases)]
    [else (get-base v (rest bases))]))

(struct opcode (name op mode modefn fn cycles) #:transparent)
(define (make-op v)
  (define b (get-base v base-opcode-list))
  (define mode (hash-ref mode-by-op-hash v 'immediate))
  (opcode (base-name b) v mode (hash-ref address-mode-functions mode) 
          (base-fn b) (hash-ref cycle-counts v 1)))

; finaly can build the complete opcodes list. 
(define opcodes (build-vector #xff make-op))
;; -----------------------------------End of 6502 instruction data----------------------------------------


; create and initialize a 6502 cpu.
(define (make-cpu) (hash))
(define (init-cpu cpu)
  (~> (poke cpu 'pc (peek-word cpu reset-vector))
      (flag-set 'u)))

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

; memory may contain mapped in sections of rom or other devices.
(struct mem-map (start end peek-fn))
(define (get-mem-maps cpu) (hash-ref cpu '_maps (hash)))
(define (add-mem-map cpu name start end peekfn)
  (hash-set cpu '_maps (hash-set (get-mem-maps cpu) name (mem-map start end peekfn))))
(define (remove-mem-map cpu name) (hash-set cpu '_maps (hash-remove (get-mem-maps cpu) name)))
(define (base-peek cpu addr) (hash-ref cpu addr 0))
; see if this address is covered by an active memory map.
(define (get-peek-fn cpu addr maps)
  (cond [(null? maps) base-peek]
        [(and (>= addr (mem-map-start (first maps))) (< addr (mem-map-end (first maps)))) 
         (mem-map-peek-fn (first maps))]
        [else (get-peek-fn cpu addr (rest maps))]))

(define (peek cpu addr) 
  ((if (number? addr) (get-peek-fn cpu addr (hash-values (get-mem-maps cpu))) base-peek) cpu addr))

(define (poke cpu addr val) (hash-set cpu addr val))
(define (inc cpu addr) (poke cpu addr (byte-add (peek cpu addr) 1)))
(define (dec cpu addr) (poke cpu addr (byte-sub (peek cpu addr) 1)))
(define (inc-word cpu addr) (poke cpu addr (word-add (peek cpu addr) 1)))
(define (dec-word cpu addr) (poke cpu addr (word-sub (peek cpu addr) 1)))
(define (peek-word cpu addr)
  (bitwise-ior (bitwise-and (peek cpu addr) #xff) 
               (arithmetic-shift  (bitwise-and (peek cpu (add1 addr)) #xff) 8)))

; accelerators 
(define (add-cycles cpu cycles) (poke cpu '_cycles (+ cycles (peek cpu '_cycles))))

(define (peek-data-address cpu) (peek cpu '_data))
(define (peek-data cpu) (peek cpu (peek cpu '_data)))
(define (peek-data-word cpu) (peek-word cpu (peek cpu '_data)))
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
(define (flag-if cpu f test) (if test (flag-set cpu f) (flag-clear cpu f)))
(define (flag-set-nz cpu addr) 
  (define val (peek cpu addr)) (~> (flag-if-zero cpu 'z val) (flag-if-has-flag 'n val)))
(define (carry-if-bit cpu bit v) (if (> (bitwise-and bit v) 0 ) (flag-set cpu 'c) (flag-clear cpu 'c)))
(define (rot-carry-bit cpu addr bit) (if (flag-set? cpu 'c) 
                                         (poke cpu addr (bitwise-ior (peek cpu addr) bit)) cpu))


(define (hex-string num width) (~a (format "~x" num) #:align 'right #:width width #:pad-string "0"))
(define (bin-string num width) (~a (format "~b" num) #:align 'right #:width width #:pad-string "0"))
(define (register-string cpu)
  (format "~a a: $~a x: $~a y: $~a sp: $~a pc: $~a cycles: ~a\n"
          (flags-string cpu)
          (hex-string (peek cpu 'a) 2) (hex-string (peek cpu 'x) 2) (hex-string (peek cpu 'y) 2)
          (hex-string (peek cpu 'sp) 2) (hex-string (peek cpu 'pc) 4) (peek cpu '_cycles)))

(define (disassemble cpu)
  (define op (peek cpu 'op))
  ((hash-ref mode-disassemble (opcode-mode op)) cpu op))

(define (disassemble-lines cpu lines [outstrings empty])
  (define d (disassemble-at-pc cpu))
  (if (= lines 0) 
      outstrings (disassemble-lines 
                  (poke cpu 'pc (word-add (peek cpu 'pc) (car d))) (- lines 1) 
                  (append outstrings (list (cdr d))))))

(define (flags-string cpu)
  (format "|~a|~a|~a|~a|~a|~a|~a|~a|"
          (if (flag-set? cpu 'n) "N" "n") (if (flag-set? cpu 'v) "V" "v") (if (flag-set? cpu 'u) "U" "u")
          (if (flag-set? cpu 'b) "B" "b") (if (flag-set? cpu 'd) "D" "d") (if (flag-set? cpu 'i) "I" "i")
          (if (flag-set? cpu 'z) "Z" "z") (if (flag-set? cpu 'c) "C" "c")))
(define (display-cpu cpu op)
  (printf "|NVUBDIZC| ~a ~a\n|~a| a: $~a x: $~a y: $~a sp: $~a pc: $~a cycles: ~a\n"
          (opcode-name op) ((hash-ref mode-disassemble (opcode-mode op)) cpu op) (bin-string (peek cpu 'ps) 8) 
          (hex-string (peek cpu 'a) 2) (hex-string (peek cpu 'x) 2) (hex-string (peek cpu 'y) 2)
          (hex-string (peek cpu 'sp) 2) (hex-string (peek cpu 'pc) 4) (peek cpu '_cycles)) cpu)

(define (load-bytes cpu address bs)
  (if (null? bs) cpu (load-bytes (poke cpu address (first bs)) (add1 address) (rest bs))))

(define (disassemble-at-pc cpu)
  (define op (vector-ref opcodes (peek cpu (peek cpu 'pc))))
  (define cpu2 
    (~> (poke cpu '_op op) 
        (inc-pc)               
        ((opcode-modefn op) _)))
  (cons (- (peek cpu2 'pc) (peek cpu 'pc)) 
        (format "$~a: ~a"
                (hex-string (peek cpu 'pc) 4)
                ((hash-ref mode-disassemble (opcode-mode op)) cpu2 op)))


)

(define (step cpu)
  (define op (vector-ref opcodes (peek cpu (peek cpu 'pc))))
  (~> (poke cpu '_op op) 
      (inc-pc)               
      ((opcode-modefn op) _)
      ((opcode-fn op) _)
      (add-cycles (opcode-cycles op))
      (display-cpu op))


  )

(define (exec cpu)
  (define op (vector-ref opcodes (peek cpu (peek cpu 'pc))))
  (if (string=? (opcode-name op) "hcf") #t (step cpu)))


(define (test-prog cpu)
  (~> 
   (load-bytes cpu 0 
               '(#xa2 10          ; LDX #10
                 #x8a             ; LOOP: TXA
                 #x20 #x00 #x10   ; JSR $1000
                 #xca             ; DEX
                 #xd0 #xf9        ; BNE LOOP
                 #xa9 #x01        ; LDA #$01
                 #x85 #xb0        ; STA $b0
                 #x06 #xb0        ; LOOP2: ASL $b0
                 #x90 #xfc        ; BCC LOOP2
                 #x0a             ; LOOP3 ASL ;'a
                 #x90 #xfd        ; BCC LOOP3      
                 ))
   (load-bytes #x1000 
               '(#x95 #xa0   ; STA $A0, X 
                 #x60        ; RTS
                 ))


))

