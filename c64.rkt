#lang racket

(require "6502.rkt" racket/file threading)
(provide make-c64)

; rom file start addresses
(define basic-rom-start #xa000)
(define kernal-rom-start #xe000)
(define char-rom-start #xd000)


(struct rom (name data start end))

(define (make-rom name path start)
  (define b (file->bytes path))
  (rom name b start (+ start (bytes-length b))))


(define roms (list (make-rom "basic" "bin/basic.bin" basic-rom-start)
                   
                   (make-rom "char" "bin/char.bin" char-rom-start)))


(define kernal-rom (make-rom "kernal" "bin/kernal.bin" kernal-rom-start))
(define (kernal-peek cpu addr)
  (bytes-ref (rom-data kernal-rom) (- addr (rom-start kernal-rom))))

(define (make-c64)
  (~> (make-cpu) 
      (add-mem-map "kernal" (rom-start kernal-rom) (rom-end kernal-rom) kernal-peek)
      (init-cpu)) 
  
)
