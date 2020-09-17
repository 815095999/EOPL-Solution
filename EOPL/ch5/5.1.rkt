#lang eopl

; procedural representation style
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
              (env environment?)))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (equal? saved-var search-var)
                      saved-val
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
  (lambda (proc1 val cont)
    (cases proc proc1
      (procedure (var body saved-env)
                 (value-of/k body
                             (extend-env var val saved-env)
                             cont)))))

; ------------------------------------------------------------------------------
; Continuation (procedural-representation)
; cont: val -> finalanswer
; end-cont: () -> cont
(define end-cont
  (lambda ()
    (lambda (val)
      (begin (eopl:printf "End of computation.~%")
             val))))

; zero1-cont: cont -> cont
(define zero1-cont
  (lambda (cont)
    (lambda (val)
      (apply-cont cont
                  (bool-val (zero? (expval->num val)))))))

; let-exp-cont: var x exp x env x cont -> cont
(define let-exp-cont
  (lambda (var exp env cont)
    (lambda (val)
      (value-of/k exp (extend-env var val env) cont))))

; if-test-cont: exp x exp x env x cont -> cont
(define if-test-cont
  (lambda (exp1 exp2 env cont)
    (lambda (val)
      (if (expval->bool val)
          (value-of/k exp1 env cont)
          (value-of/k exp2 env cont)))))

; diff1-cont: exp x env x cont -> cont
(define diff1-cont
  (lambda (exp env cont)
    (lambda (val)
      (value-of/k exp env (diff2-cont val cont)))))
; diff2-cont: expval x cont -> cont
(define diff2-cont
  (lambda (val1 cont)
    (lambda (val2)
      (apply-cont cont (num-val (- (expval->num val1)
                                   (expval->num val2)))))))

; rator-cont: exp x env x cont -> cont
(define rator-cont
  (lambda (exp env cont)
    (lambda (val)
      (value-of/k exp env (rand-cont val cont)))))
; rand-cont: expval x cont -> cont
(define rand-cont
  (lambda (proc cont)
    (lambda (val)
      (let ((proc1 (expval->proc proc)))
        (apply-procedure/k proc1 val cont)))))
; apply-cont: cont x val -> finalanswer
(define apply-cont
  (lambda (cont val)
    (cont val)))
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
        (value-of/k exp1 (init-env) (end-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var)
               (apply-cont cont (apply-env env var)))
      (proc-exp (var body)
                (apply-cont cont (proc-val (procedure var body env))))
      (zero?-exp (exp1)
                 (value-of/k exp1 env (zero1-cont cont)))
      (let-exp (var exp body)
               (value-of/k exp env (let-exp-cont var body env cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
      (diff-exp (exp1 exp2)
        (value-of/k exp1 env (diff1-cont exp2 env cont)))
      (call-exp (rator rand)
                (value-of/k rator env (rator-cont rand env cont)))
      )))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))

(run "let d = proc (x) proc (y) if zero?(x) then -(0,y) else y in ((d 0) 4)")