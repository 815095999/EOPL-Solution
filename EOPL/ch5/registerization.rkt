#lang eopl

; registerization
; ------------------------------------------------------------------------------
; Environments
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define-datatype environment environment?
  (empty-env)
  (extend-env (var identifier?)
              (val expval?)
              (env environment?))
   (extend-env-rec (p-name identifier?)
                   (b-var identifier?)
                   (body expression?)
                   (saved-env environment?)))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (equal? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-name b-var body saved-env)
                           (if (equal? search-var p-name)
                               (proc-val (procedure b-var body env))
                               (apply-env saved-env search-var))))))
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define init-env
  (lambda ()
    (extend-env 'i (num-val 1)
      (extend-env 'v (num-val 5)
        (extend-env 'x (num-val 10)
          (empty-env))))))
; ------------------------------------------------------------------------------
; Scanner and parser specification

(define scanner-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

; ------------------------------------------------------------------------------
; Debugging helpers for scanner and parser

(define list-the-datatypes
  (lambda()
    (sllgen:list-define-datatypes scanner-spec grammar)))

(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar))

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

; ------------------------------------------------------------------------------
; Expressed values
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?)))

; expval->num: expval -> num
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
; expval->bool: expval -> bool
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))
; expval->proc: expval -> proc
(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc1) proc1)
      (else (report-expval-extractor-error 'proc-val val)))))
(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

; ------------------------------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure (var identifier?)
             (body expression?)
             (saved-env environment?)))

; apply-procedure: proc x val x cont -> finalanswer
(define apply-procedure/k
  (lambda ()
    (cases proc proc1
      (procedure (var body saved-env)
                 (set! exp body)
                 (set! env (extend-env var val saved-env))
                 (value-of/k)))))


; ------------------------------------------------------------------------------
; register
(define exp 'uninitialized)
(define env 'uninitialized)
(define cont 'uninitialized)
(define val 'uninitialized)
(define proc1 'uninitialized)

; ------------------------------------------------------------------------------
; Continuation (data-structure representation)
; cont: val -> finalanswer
; end-cont: () -> cont
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont (cont continuation?))
  (let-exp-cont (var identifier?)
                (body expression?)
                (env environment?)
                (cont continuation?))
  (if-test-cont (exp1 expression?)
                (exp2 expression?)
                (env environment?)
                (cont continuation?))
  (diff1-cont (exp2 expression?)
              (env environment?)
              (cont continuation?))
  (diff2-cont (val1 expval?)
              (cont continuation?))
  (rator-cont (rand expression?)
              (env environment?)
              (cont continuation?))
  (rand-cont (rator expval?)
             (cont continuation?))
  )

; apply-cont: cont x val -> finalanswer
(define apply-cont
  (lambda ()
    (cases continuation cont
      (end-cont ()
                (eopl:printf "End of computation.~%")
                val)
      (zero1-cont (saved-cont)
                  (set! cont saved-cont)
                  (set! val (bool-val (zero? (expval->num val))))
                  (apply-cont))
      (let-exp-cont (var body saved-env saved-cont)
                    (set! cont saved-cont)
                    (set! exp body)
                    (set! env (extend-env var val saved-env))
                    (value-of/k))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (set! cont saved-cont)
                    (if (expval->bool val)
                        (set! exp exp2)
                        (set! exp exp3))
                    (set! env saved-env)
                    (value-of/k))
      (diff1-cont (exp2 saved-env saved-cont)
                  (set! cont (diff2-cont val saved-cont))
                  (set! exp exp2)
                  (set! env saved-env)
                  (value-of/k))
      (diff2-cont (val1 saved-cont)
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val)))
                    (set! cont saved-cont)
                    (set! val (num-val (- num1 num2)))
                    (apply-cont)))
      (rator-cont (rand saved-env saved-cont)
                  (set! cont (rand-cont val saved-cont))
                  (set! exp rand)
                  (set! env saved-env)
                  (value-of/k))
      (rand-cont (rator-val saved-cont)
                 (let ((rator-proc (expval->proc rator-val)))
                   (set! cont saved-cont)
                   (set! proc1 rator-proc)
                   (set! val val)
                   (apply-procedure/k))))))

; ------------------------------------------------------------------------------
; Interpreter

; run: string -> finalanswer
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program: program -> finalanswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (set! cont (end-cont))
                 (set! exp exp1)
                 (set! env (init-env))
                 (value-of/k)))))

(define value-of/k
  (lambda ()
    (cases expression exp
      (const-exp (num)
                 (set! val (num-val num))
                 (apply-cont))
      (var-exp (var)
               (set! val (apply-env env var))
               (apply-cont))
      (proc-exp (var body)
                (set! val (proc-val (procedure var body env)))
                (apply-cont))
      (letrec-exp (p-name b-var p-body letrec-body)
                  (set! exp letrec-body)
                  (set! env (extend-env-rec p-name b-var p-body env))
                  (value-of/k))
      (zero?-exp (exp1)
                 (set! cont (zero1-cont cont))
                 (set! exp exp1)
                 (value-of/k))
      (let-exp (var exp1 body)
               (set! cont (let-exp-cont var body env cont))
               (set! exp exp1)
               (value-of/k))
      (if-exp (exp1 exp2 exp3)
              (set! cont (if-test-cont exp2 exp3 env cont))
              (set! exp exp1)
              (value-of/k))
      (diff-exp (exp1 exp2)
                (set! cont (diff1-cont exp2 env cont))
                (set! exp exp1)
                (value-of/k))
      (call-exp (rator rand)
                (set! cont (rator-cont rand env cont))
                (set! exp rator)
                (value-of/k))
      )))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))

(run "let d = proc (x) proc (y) if zero?(x) then -(0,y) else y in ((d 0) 4)")