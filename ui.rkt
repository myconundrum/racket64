#lang racket/gui

(require "6502.rkt" "c64.rkt" threading )

(define (hit-breakpoint? s)
  (member (peek (state-c64 s) 'pc) (state-breakpoints s)))

(provide 
 show-ui)

(define (handle-event s name value)
  (case name
    ['add-breakpoint (struct-copy state s [breakpoints (cons value (state-breakpoints s))])]
    ['remove-breakpoint (struct-copy state s [breakpoints (delete-at-index (state-breakpoints s) value)])]
    ['toggle-breakpoint s ]; BUGBUG unimplemented.
    ['set-page (struct-copy state s [page value])]
    ['add-watch (struct-copy state s [watches (cons value (state-watches s))])]
    ['remove-watch (struct-copy state s [watches (delete-at-index (state-watches s) value)])]
    ['step-c64 (struct-copy state s [c64 (step (state-c64 s))])]
    ['stop-c64 (struct-copy state s [running #f])]
    ['run-c64 (struct-copy state s [running #t])]
    [else s]))

(define (render state)
  (update-ui state))

(struct state (c64 running breakpoints watches page) #:transparent)

(define (make-state) (state (make-c64) false null null #x00))


(define (set-flags cpu64)
  (hash-for-each flags-hash (λ (k v) (send v set-value (flag-set? cpu64 k)))))

(define (memory-string-line s start)
  (for/fold ([str (format "$~a:" (hex-string start 4))]) ([c (range 16)])
    (string-append str (format " ~a" (hex-string (peek (state-c64 s) (+ start c)) 2)))))

(define (is-ascii-print? v) (and (> v 31) (< v 127)))
(define (memory-chars-line s start)
  (for/fold ([str ""]) ([c (range 16)])
    (define ch (peek (state-c64 s) (+ start c)))
    (string-append str (if (is-ascii-print? ch) (format "~a" (integer->char ch)) "."))))

(define (show-page s)
  (define c64 (state-c64 s))
  (send memory set null)
  (for ([r (range 16)])
    (define start (+ (state-page s) (* r 16)))
    (send memory append (format "~a ~a" (memory-string-line s start) (memory-chars-line s start)))))

(define (show-watches s)
  (define c64 (state-c64 s))
  (send watch-win set 
        (for/fold ([strs null]) ([w (state-watches s)])
          (cons (format "$~a\t$~a" (hex-string w 4) (hex-string (peek c64 w) 2)) strs))))

(define (update-ui s)
  (send disassembly set (disassemble-lines (state-c64 s) 20))
  (send disassembly select 0)
  (send registers set (register-strings (state-c64 s)))
  (send cycles set-value (format "~a" (peek (state-c64 s) '_cycles)))
  (set-flags (state-c64 s))
  (show-page s)
  (send frame set-status-text (if  (state-running s) "Running." "Stopped."))
  (send breakpoints set (map (λ (v) (number->string v 16)) (state-breakpoints s)))
  (show-watches s)
  s
)


(define (show-ui)
  (send frame show #t)
  (run-state (make-state)))


; state machine uses this variable to keep track of ui-control events between function calls.
(define event-queue null)
(struct state-event (name data))
(define (add-event name data) (set! event-queue (append event-queue (list (state-event name data)))))

(define (handle-all-events ui)
  (define events event-queue)
  (set! event-queue null)
  (for/fold ([rui ui]) ([e events])
    (handle-event rui (state-event-name e) (state-event-data e))))

(define (update-c64 ui) (if (state-running ui) (struct-copy state ui [c64 (step (state-c64 ui))]) ui ))
(define (check-breakpoints ui) 
  (if (and (state-running ui) (hit-breakpoint? ui)) (struct-copy state ui [running false]) ui))

(define (run-state ui)
  (sleep/yield .1)
  (run-state (~> (handle-all-events ui)
                 (check-breakpoints)
                 (update-c64)
                 (update-ui))))


(define (delete-at-index l i)
  (cond [(= i 0) (rest l)]
        [(< i (length l)) (append (take l i) (rest (drop l i)))]
        [else l]))

(define (hex-string num width) (~a (format "~x" num) #:align 'right #:width width #:pad-string "0"))
(define (bin-string num width) (~a (format "~b" num) #:align 'right #:width width #:pad-string "0"))

(define (register-strings c64)
  (list 
   "reg\thex\t\tbin"
   (format "a\t$~a\t\t~a" (hex-string (peek c64 'a) 2) (bin-string (peek c64 'a) 8)) 
   (format "x\t$~a\t\t~a" (hex-string (peek c64 'x) 2) (bin-string (peek c64 'x) 8)) 
   (format "y\t$~a\t\t~a" (hex-string (peek c64 'y) 2) (bin-string (peek c64 'y) 8)) 
   (format "sp\t$~a\t\t~a" (hex-string (peek c64 'sp) 2) (bin-string (peek c64 'sp) 8)) 
   (format "ps\t$~a\t\t~a" (hex-string (peek c64 'ps) 2) (bin-string (peek c64 'ps) 8)) 
   (format "pc\t$~a\t~a" (hex-string (peek c64 'pc) 4) (bin-string (peek c64 'pc) 16)) ))




;--------------------Global UI Widgets----------------------------
(define the-font (send the-font-list find-or-create-font 13 #f 'modern))
(define frame (new frame% [label "Racket 64"] [width 1024] [height 600]))
(define main-area (new horizontal-pane% [alignment (list 'left 'top)] [parent frame]))
(define registers-area (new group-box-panel% [parent main-area] [label "Registers"]
                            [alignment (list 'left 'top) ] [stretchable-width false] [stretchable-height false]))
(define registers (new list-box% [parent registers-area]
                      [label ""]
                      [enabled false]
                      [font the-font]
                      [min-width (* 22 12)]
                      [min-height (* 12 12)]
                      [stretchable-width false]
                      [stretchable-height false]
                      [choices null]))
(define cycles (new text-field% 
                    [parent registers-area] [label "cycles"] [enabled false]
                    [min-width (* 10 12)]
                    [font the-font]
                    [stretchable-height false]
                    [stretchable-width false]))
(define flags-area (new horizontal-pane% [stretchable-width false] [stretchable-height false] 
                        [parent registers-area]))
(define flags-hash
  (hash 'n (new check-box% [label "n"] [parent flags-area])
        'v (new check-box% [label "v"] [parent flags-area])
        'u (new check-box% [label "u"] [parent flags-area])
        'b (new check-box% [label "b"] [parent flags-area])
        'd (new check-box% [label "d"] [parent flags-area])
        'i (new check-box% [label "i"] [parent flags-area])
        'z (new check-box% [label "z"] [parent flags-area])
        'c (new check-box% [label "c"] [parent flags-area])))

(define disassembly-area (new group-box-panel% 
                              [label "Disassembly"] [parent main-area]
                              [stretchable-width false] [stretchable-height false]
                              [alignment (list 'left 'top) ]))
(define disassembly (new list-box% [parent disassembly-area]
                      [label ""]
                      [font the-font]
                      [enabled false]
                      [min-width (* 22 12)]
                      [min-height (* 29 12)]
                      [stretchable-width false]
                      [stretchable-height false]
                      [choices null]))


(define add-bp (new text-field% [parent disassembly-area] [label "Add Breakpoint"] 
                    [callback (λ (tf evt) 
                                (when (equal? (send evt get-event-type) 'text-field-enter)
                                  (add-event 'add-breakpoint (string->number (send tf get-value) 16)) 
                                  (send add-bp set-value "")))]
                    [font the-font]
                    [min-width (* 5 12)]
                    [stretchable-width false] [stretchable-height false]))
(define breakpoints (new list-box% [parent disassembly-area]
                      [label ""]
                      [font the-font]
                      [min-width (* 22 12)]
                      [min-height (* 10 12)]
                      [stretchable-width false]
                      [stretchable-height false]
                      [choices null]))

(define bp-buttons (new horizontal-panel% [parent disassembly-area] [vert-margin 0]))
(define remove-bp-button (new button% [parent bp-buttons] [label "Remove"]
                              [callback (λ (btn evt) 
                                          (when (send breakpoints get-selection) 
                                            (add-event 'remove-breakpoint 
                                                       (send breakpoints get-selection))))]))



(define toggle-bp-button (new button% [parent bp-buttons] [label "Toggle"]
                              [callback (λ (btn evt) 
                                          (when (send breakpoints get-selection) 
                                            (add-event 'toggle-breakpoint 
                                                       (send breakpoints get-selection))))]))


(define memory-area (new group-box-panel% [parent main-area] [label "Memory"]
                         [alignment (list 'left 'top) ] [stretchable-width false] [stretchable-height false]))

(define page (new text-field% [parent memory-area] [label "page"] 
                  [font the-font]
                  [min-width (* 5 12)]
                  [stretchable-width false] [stretchable-height false]
                  [callback (λ (tf evt) 
                              (when (equal? (send evt get-event-type) 'text-field-enter)
                                (add-event 'set-page (string->number (send tf get-value) 16)) 
                                (send page set-value "")) )]))

(define memory (new list-box% [parent memory-area]
                      [label ""]
                      [enabled false]
                      [font the-font]
                      [min-width (* 60 12)]
                      [min-height (* 26 12)]
                      [stretchable-width false]
                      [stretchable-height false]
                      [choices null]))



(define add-watch (new text-field% [parent memory-area] [label "Add Watch"] 
                       [callback (λ (tf evt) 
                                   (when (equal? (send evt get-event-type) 'text-field-enter)
                                     (add-event 'add-watch (string->number (send tf get-value) 16))
                                     (send add-watch set-value "")))]
                    [font the-font]
                    [min-width (* 5 12)]
                    [stretchable-width false] [stretchable-height false]))

(define watch-win (new list-box% [parent memory-area]
                      [label ""]
                      [font the-font]
                      [min-width (* 22 12)]
                      [min-height (* 10 12)]
                      [stretchable-width false]
                      [stretchable-height false]
                      [choices null]))



(define watch-buttons (new horizontal-panel% [parent memory-area] [vert-margin 0]))

(define remove-watch-button (new button% [parent watch-buttons] [label "Remove"]
                                 [callback (λ (btn evt) 
                                             (when (send watch-win get-selection)
                                               (add-event 'remove-watch (send watch-win get-selection))))]))



(define cmd (new text-field% [parent frame] 
                 [label "Command"]
                 [callback (λ (tf evt) 
                                   (when (equal? (send evt get-event-type) 'text-field-enter)
                                     (add-event 'add-command (send tf get-value)) 
                                     (send tf set-value "")))]))

(define buttons (new horizontal-panel% [parent frame] [vert-margin 0]))
(define step-button (new button% [parent buttons] [label "Step"]
                         [callback (λ (btn evt) (add-event 'step-c64 #t))]))
(define run-button (new button% [parent buttons] [label "Run"]
                         [callback (λ (btn evt) (add-event 'run-c64 #t))]))
(define stop-button (new button% [parent buttons] [label "Stop"]
                         [callback (λ (btn evt) (add-event 'stop-c64 #t))]))

