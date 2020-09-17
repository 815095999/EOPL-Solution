#lang eopl
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
  (extend-env-rec (p-names (list-of identifier?))
                  (vectors (list-of vector?)) (env environment?)))
(define extend-env-rec*
  (lambda (p-names b-vars bodys env)
    (define (generate-vec num)
      (if (= num 0)
          '()
          (cons (make-vector 1) (generate-vec (- num 1)))))
    (define vecs (generate-vec (length p-names)))
    (define new-env (extend-env-rec p-names vecs env))
    (define (modify-vec vecs b-vars bodys env num)
      (if (null? b-vars)
          env
          (begin (vector-set! (list-ref vecs num) 0
                              (proc-val (procedure (car b-vars) (car bodys) env)))
                 (modify-vec vecs (cdr b-vars) (cdr bodys) env (+ num 1)))))
    (modify-vec vecs b-vars bodys new-env 0)))
(define extend-env-let
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars) (car vals)
                    (extend-env-let (cdr vars) (cdr vals) env)))))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (equal? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-names vecs saved-env)
                      (if (memq search-var p-names)
                          (extract-procedure p-names vecs search-var 0)
                          (apply-env saved-env search-var))))))
(define extract-procedure
  (lambda (p-names vecs search-var num)
    (if (equal? search-var (car p-names))
        (vector-ref (list-ref vecs num) 0)
        (extract-procedure (cdr p-names) vecs search-var (+ num 1)))))
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
  '((program (tfexp) a-program)
    (simple-exp (number) const-exp)
    (simple-exp (identifier) var-exp)
    (simple-exp ("-" "(" simple-exp "," simple-exp ")") cps-diff-exp)
    (simple-exp ("zero?" "(" simple-exp ")") cps-zero?-exp)
    (tfexp (simple-exp) simple-exp->exp)
    (tfexp ("let" (arbno identifier "=" simple-exp) "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" tfexp) "in" tfexp) cps-letrec-exp)
    (tfexp ("(" simple-exp (arbno simple-exp) ")") cps-call-exp)
    (tfexp ("if" simple-exp "then" tfexp "else" tfexp) cps-if-exp)
    (simple-exp ("proc" "(" (separated-list identifier ",") ")" tfexp) cps-proc-exp)
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
  (procedure (var (list-of identifier?))
             (body tfexp?)
             (saved-env environment?)))

; apply-procedure: proc x val x cont -> finalanswer
(define apply-procedure/k
  (lambda (proc1 vals cont)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body
                             (extend-env-let vars vals saved-env)
                             cont)))))


; ------------------------------------------------------------------------------
; Interpreter

(define apply-cont
  (lambda (x val)
    val))
; run: string -> finalanswer
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program: program -> finalanswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of/k exp1 (init-env) 0)))))

(define value-of/k
  (lambda (exp env cont)
    (cases tfexp exp
      (simple-exp->exp (simple)
                       (apply-cont cont (value-of-simple-exp simple env)))
      (cps-let-exp (vars rhs body)
               (let ((vals (map (lambda (x) (value-of-simple-exp x env)) rhs)))
                 (value-of/k body (extend-env-let vars vals env) cont)))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                  (value-of/k letrec-body (extend-env-rec* p-names b-varss p-bodies env) cont))
      (cps-if-exp (simple1 body1 body2)
              (if (expval->bool (value-of-simple-exp simple1 env))
                  (value-of/k body1 env cont)
                  (value-of/k body2 env cont)))
      (cps-call-exp (rator rands)
                (let ((rator-proc (expval->proc (value-of-simple-exp rator env)))
                      (rand-vals (map (lambda (simple) (value-of-simple-exp simple env)) rands)))
                  (apply-procedure/k rator-proc rand-vals cont))))))
(define value-of-simple-exp
  (lambda (exp env)
    (cases simple-exp exp
      (const-exp (num) (num-val num))
      (var-exp (var) (apply-env env var))
      (cps-diff-exp (exp1 exp2)
                    (let ((val1 (value-of-simple-exp exp1 env))
                          (val2 (value-of-simple-exp exp2 env)))
                      (num-val (- (expval->num val1)
                                  (expval->num val2)))))
      (cps-zero?-exp (exp1)
                     (let ((val1 (value-of-simple-exp exp1 env)))
                       (if (= (expval->num val1) 0)
                           (bool-val #t)
                           (bool-val #f))))
      (cps-proc-exp (vars body)
                    (proc-val (procedure vars body env))))))
(run "let x = 3 y = proc (x) -(x,5) in (y x)")
(run "letrec odd(x,y)=if zero?(x) then 0 else (even -(x,1) y)
                even(x,y)= if zero?(x) then 1 else (odd -(x,1) y) in (odd 101 0)")
