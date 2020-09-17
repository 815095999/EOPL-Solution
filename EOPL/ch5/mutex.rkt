#lang eopl

; -----------------------------------------------------------
; Grammar

(define the-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define the-grammar
  '([program (expression) a-program]
    [expression (number) const-exp]
    [expression ("-" "(" expression "," expression ")") diff-exp]
    [expression ("*" "(" expression "," expression ")") multiply-exp]
    [expression ("zero?" "(" expression ")") zero?-exp]
    [expression ("if" expression "then" expression "else" expression) if-exp]
    [expression (identifier) var-exp]
    [expression ("let" identifier "=" expression "in" expression) let-exp]
    [expression ("proc" "(" identifier ")" expression) proc-exp]
    [expression ("(" expression expression ")") call-exp]
    [expression ("letrec" (arbno identifier "(" identifier ")" "=" expression) "in" expression) letrec-exp]
    [expression ("begin" expression (arbno ";" expression) "end") begin-exp]
    [expression ("set" identifier "=" expression) assign-exp]
    [expression ("print" "(" expression")") print-exp]
    [expression ("spawn" "(" expression ")") spawn-exp]
    [expression ("mutex" "(" ")") mutex-exp]
    [expression ("wait" "(" expression ")") wait-exp]
    [expression ("signal" "(" expression ")") signal-exp]
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

; -----------------------------------------------------------
; mutex
(define-datatype mutex mutex?
  (a-mutex
   (ref-to-closed? reference?)
   (ref-to-wait-queue reference?)))

; new-mutex : () -> mutex
(define new-mutex
  (lambda ()
    (a-mutex (newref #f) (newref '()))))

; wait-for-mutex : mutex x thread -> finalanswer
(define wait-for-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (cond ((deref ref-to-closed?)
                      (setref! ref-to-wait-queue
                               (enqueue (deref ref-to-wait-queue) th))
                      (run-next-thread))
                     (else
                      (setref! ref-to-closed? #t)
                      (th)))))))
; signal-mutex : mutex x thread -> finalanswer
(define signal-mutex
  (lambda (m th)
    (cases mutex m
      (a-mutex (ref-to-closed? ref-to-wait-queue)
               (let ((closed? (deref ref-to-closed?))
                     (wait-queue (deref ref-to-wait-queue)))
                 (cond (closed?
                        (if (empty? wait-queue)
                            (setref! ref-to-closed? #f)
                            (dequeue wait-queue
                                     (lambda (fir sec)
                                       (place-on-ready-queue! fir)
                                       (setref! ref-to-wait-queue sec))))))
                 (th))))))


; -----------------------------------------------------------
; data structure

(define identifier? symbol?)
(define reference? integer?)

(define-datatype proc proc?
  [procedure [bvar symbol?]
             [body expression?]
             [env environment?]])

(define-datatype expval expval?
  [num-val [value number?]]
  [bool-val [boolean boolean?]]
  [proc-val [proc proc?]]
  [mutex-val [mutex1 mutex?]])

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s" variant value)))

(define expval->num
  (lambda (v)
    (cases expval v
      [num-val (num) num]
      [else (expval-extractor-error 'num v)])))

(define expval->bool
  (lambda (v)
    (cases expval v
      [bool-val (bool) bool]
      [else (expval-extractor-error 'bool v)])))

(define expval->proc
  (lambda (v)
    (cases expval v
      [proc-val (proc) proc]
      [else (expval-extractor-error 'proc v)])))

(define expval->mutex
  (lambda (v)
    (cases expval v
      [mutex-val (mutex1) mutex1]
      [else (expval-extractor-error 'mutex v)])))

(define-datatype environment environment?
  [empty-env]
  [extend-env [bvar symbol?]
              [bval reference?]
              [saved-env environment?]]
  [extend-env-rec* [proc-names (list-of symbol?)]
                   [b-vars (list-of symbol?)]
                   [proc-bodies (list-of expression?)]
                   [saved-env environment?]])

(define-datatype continuation continuation?
  [end-cont]
  [zero1-cont [saved-cont continuation?]]
  [let-exp-cont [var identifier?]
                [body expression?]
                [saved-env environment?]
                [saved-cont continuation?]]
  [if-test-cont [exp2 expression?]
                [exp3 expression?]
                [saved-env environment?]
                [saved-cont continuation?]]
  [diff1-cont [exp2 expression?]
              [saved-env environment?]
              [saved-cont continuation?]]
  [diff2-cont [val1 expval?]
              [saved-cont continuation?]]
  [multiply1-cont [exp2 expression?]
                  [saved-env environment?]
                  [saved-cont continuation?]]
  [multiply2-cont [val1 expval?]
                  [saved-cont continuation?]]
  [rator-cont [rand expression?]
              [saved-env environment?]
              [saved-cont continuation?]]
  [rand-cont [val1 expval?]
             [saved-cont continuation?]]
  [begin-cont [exps (list-of expression?)]
              [saved-env environment?]
              [saved-cont continuation?]]
  [set-rhs-cont [ref reference?]
                [saved-cont continuation?]]
  [spawn-cont [cont continuation?]]
  [print-cont [cont continuation?]]
  [end-main-thread-cont]
  [end-subthread-cont]
  [wait-cont [cont continuation?]]
  [signal-cont [cont continuation?]])


; -----------------------------------------------------------
; Store

(define the-store 'uninitialized)

(define empty-store
  (lambda ()
    '()))

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref "illegal reference ~s in store ~s" ref the-store)))

(define setref!
  (lambda (ref val)
    (set! the-store (letrec ([setref-inner (lambda (store1 ref1)
                                             (cond [(null? store1) (report-invalid-reference ref the-store)]
                                                   [(zero? ref1) (cons val (cdr store1))]
                                                   [else (cons (car store1) (setref-inner (cdr store1) (- ref1 1)))]))])
                      (setref-inner the-store ref)))))

; -----------------------------------------------------------
; scheduler

(define empty-queue
  (lambda ()
    '()))

(define empty? null?)

(define enqueue
  (lambda (q val)
    (append q (list val))))

(define dequeue
  (lambda (q f)
    (f (car q) (cdr q))))

(define the-ready-queue 'uninitialized)
(define the-final-answer 'uninitialized)
(define the-max-time-slice 'uninitialized)
(define the-time-remaining 'uninitialized)

(define initialize-scheduler!
  (lambda (ticks)
    (set! the-ready-queue (empty-queue))
    (set! the-final-answer 'uninitialized)
    (set! the-max-time-slice ticks)
    (set! the-time-remaining the-max-time-slice)))
(define place-on-ready-queue!
  (lambda (th)
    (set! the-ready-queue (enqueue the-ready-queue th))))
(define run-next-thread
  (lambda ()
    (if (empty? the-ready-queue)
        the-final-answer
        (dequeue the-ready-queue
                 (lambda (first-ready-thread other-ready-threads)
                   (set! the-ready-queue other-ready-threads)
                   (set! the-time-remaining the-max-time-slice)
                   (first-ready-thread))))))
(define set-final-answer!
  (lambda (val)
    (display "final-answer: ")
    (display val)
    (newline)
    (set! the-final-answer val)))
(define time-expired?
  (lambda ()
    (zero? the-time-remaining)))
(define decrement-timer!
  (lambda ()
    (set! the-time-remaining (- the-time-remaining 1))))

; -----------------------------------------------------------
; Interpreter.

(define apply-procedure/k
  (lambda (proc1 arg cont)
    (cases proc proc1
      [procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var (newref arg) saved-env)
                             cont)])))

(define used-end-conts '())

(define apply-cont
  (lambda (cont val)
    (if (time-expired?)
        (begin (place-on-ready-queue! (lambda () (apply-cont cont val)))
               (run-next-thread))
        (begin
          (decrement-timer!)
          (cases continuation cont
            [end-cont ()
                      (if (memq cont used-end-conts)
                          (eopl:error "Continuation is already used.")
                          (begin (set! used-end-conts (cons cont used-end-conts))
                                 val))]
            [zero1-cont (saved-cont)
                        (apply-cont saved-cont (bool-val (zero? (expval->num val))))]
            [let-exp-cont (var body saved-env saved-cont)
                          (value-of/k body
                                      (extend-env var (newref val) saved-env)
                                      saved-cont)]
            [if-test-cont (exp2 exp3 saved-env saved-cont)
                          (if (expval->bool val)
                              (value-of/k exp2 saved-env saved-cont)
                              (value-of/k exp3 saved-env saved-cont))]
            [diff1-cont (exp2 saved-env saved-cont)
                        (value-of/k exp2 saved-env (diff2-cont val saved-cont))]
            [diff2-cont (val1 saved-cont)
                        (let ([num1 (expval->num val1)]
                              [num2 (expval->num val)])
                          (apply-cont saved-cont (num-val (- num1 num2))))]
            [multiply1-cont (exp2 saved-env saved-cont)
                            (value-of/k exp2 saved-env (multiply2-cont val saved-cont))]
            [multiply2-cont (val1 saved-cont)
                            (let ([num1 (expval->num val1)]
                                  [num2 (expval->num val)])
                              (apply-cont saved-cont (num-val (* num1 num2))))]
            [rator-cont (rand saved-env saved-cont)
                        (value-of/k rand saved-env (rand-cont val saved-cont))]
            [rand-cont (val1 saved-cont)
                       (let ([proc (expval->proc val1)])
                         (apply-procedure/k proc val saved-cont))]
            [begin-cont (exps saved-env saved-cont)
                        (if (null? exps)
                            (apply-cont saved-cont val)
                            (value-of/k (car exps)
                                        saved-env
                                        (begin-cont (cdr exps)
                                                    saved-env
                                                    saved-cont)))]
            [set-rhs-cont (ref saved-cont)
                          (setref! ref val)
                          (apply-cont saved-cont (num-val 27))]
            [print-cont (cont)
                        (display val)
                        (newline)
                        (apply-cont cont val)]
            [spawn-cont (cont)
                        (let ((proc1 (expval->proc val)))
                          (place-on-ready-queue! (lambda ()
                                                   (apply-procedure/k proc1 (num-val 28) (end-subthread-cont)))))
                        (apply-cont cont (num-val 73))]
            [end-main-thread-cont ()
                                  (set-final-answer! val)
                                  (run-next-thread)]

            [end-subthread-cont ()
                                (run-next-thread)]
            [wait-cont (saved-cont)
                       (wait-for-mutex (expval->mutex val)
                                       (lambda () (apply-cont saved-cont (num-val 52))))]
            [signal-cont (saved-cont)
                         (signal-mutex (expval->mutex val)
                                       (lambda () (apply-cont saved-cont (num-val 53))))]
            )))))

(define location
  (lambda (sym syms)
    (cond [(null? syms) #f]
          [(eqv? sym (car syms)) 0]
          [(location sym (cdr syms)) => (lambda (n)
                                          (+ n 1))]
          [else #f])))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      [empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-var)]
      [extend-env (bvar bval saved-env)
                  (if (eqv? search-var bvar)
                      bval
                      (apply-env saved-env search-var))]
      [extend-env-rec* (p-names b-vars p-bodies saved-env)
                       (let ([n (location search-var p-names)])
                         (if n
                             (newref (proc-val (procedure (list-ref b-vars n)
                                                          (list-ref p-bodies n)
                                                          env)))
                             (apply-env saved-env search-var)))])))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      [const-exp (num)
                 (apply-cont cont (num-val num))]
      [var-exp (var)
               (apply-cont cont (deref (apply-env env var)))]
      [proc-exp (var body)
                (apply-cont cont (proc-val (procedure var body env)))]
      [letrec-exp (p-names b-vars p-bodies letrec-body)
                  (value-of/k letrec-body
                              (extend-env-rec* p-names b-vars p-bodies env)
                              cont)]
      [zero?-exp (exp1)
                 (value-of/k exp1 env (zero1-cont cont))]
      [let-exp (var exp1 body)
               (value-of/k exp1 env (let-exp-cont var body env cont))]
      [if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env (if-test-cont exp2 exp3 env cont))]
      [diff-exp (exp1 exp2)
                (value-of/k exp1 env (diff1-cont exp2 env cont))]
      [multiply-exp (exp1 exp2)
                    (value-of/k exp1 env (multiply1-cont exp2 env cont))]
      [call-exp (rator rand)
                (value-of/k rator env (rator-cont rand env cont))]
      [begin-exp (exp1 exps)
                 (value-of/k exp1 env (begin-cont exps env cont))]
      [assign-exp (var exp1)
                  (value-of/k exp1 env (set-rhs-cont (apply-env env var) cont))]
      [spawn-exp (exp1)
                 (value-of/k exp1 env (spawn-cont cont))]
      [print-exp (exp1)
                 (value-of/k exp1 env (print-cont cont))]
      [mutex-exp ()
                 (apply-cont cont (mutex-val (new-mutex)))]
      [wait-exp (exp1)
                (value-of/k exp1 env (wait-cont cont))]
      [signal-exp (exp1)
                  (value-of/k exp1 env (signal-cont cont))]
)))


(define (init-env)
  (empty-env))

(define value-of-program
  (lambda (timeslice pgm)
    (initialize-store!)
    (initialize-scheduler! timeslice)
    (cases program pgm
      [a-program (exp1) (value-of/k exp1
                                    (init-env)
                                    (end-main-thread-cont))])))

;; Interface.

(define run
  (lambda (string)
    (value-of-program 2 (scan&parse string))))

(run "let x = 0
      in let mut = mutex()
         in let incr_x = proc (id) proc (dummy) begin wait(mut); set x = -(x,-1); signal(mut) end
         in begin
              spawn((incr_x 100));
              spawn((incr_x 200));
            x
      end")
