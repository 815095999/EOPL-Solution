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
    (simple-exp ("*" "(" simple-exp "," simple-exp ")") cps-mul-exp)
    (simple-exp ("zero?" "(" simple-exp ")") cps-zero?-exp)
    (tfexp (simple-exp) simple-exp->exp)
    (tfexp ("let" (arbno identifier "=" simple-exp) "in" tfexp) cps-let-exp)
    (tfexp ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" tfexp) "in" tfexp) cps-letrec-exp)
    (tfexp ("(" simple-exp (arbno simple-exp) ")") cps-call-exp)
    (tfexp ("if" simple-exp "then" tfexp "else" tfexp) cps-if-exp)
    (simple-exp ("proc" "(" (separated-list identifier ",") ")" tfexp) cps-proc-exp)
    (simple-exp ("cons" "(" simple-exp "," simple-exp ")") cons-exp)
    (simple-exp ("car" "(" simple-exp ")") car-exp)
    (simple-exp ("cdr" "(" simple-exp ")") cdr-exp)
    (simple-exp ("null?" "(" simple-exp ")") null-exp)
    (simple-exp ("emptylist") emptylist-exp)
    (simple-exp ("list" "(" (separated-list simple-exp ",") ")") list-exp)
    (simple-exp ("equal?" "(" simple-exp "," simple-exp ")") equal-exp)
    (simple-exp ("append" "(" simple-exp "," simple-exp ")") append-exp)
    (simple-exp ("pair?" "(" simple-exp ")") pair?-exp)
    (simple-exp ("less?" "(" simple-exp "," simple-exp ")") less-exp)
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
  (proc-val (proc proc?))
  (pair-val (car1 expval?)
            (cdr1 expval?))
  (emptylist-val))

(define list-val
  (lambda (vals)
    (if (null? vals)
        (emptylist-val)
        (pair-val (car vals)
                  (list-val (cdr vals))))))
(define append-val
  (lambda (val1 val2)
    (cases expval val1
      (emptylist-val () val2)
      (pair-val (car1 cdr1)
                (pair-val car1
                          (append-val cdr1 val2)))
      (else (eopl:error 'append-val "append value error ~s" val1)))))
; expval->car: expval -> expval
(define expval->car
  (lambda (val)
    (cases expval val
      (pair-val (car1 cdr1) car1)
      (else (report-expval-extractor-error 'pair val)))))
; expval->cdr: expval -> expval
(define expval->cdr
  (lambda (val)
    (cases expval val
      (pair-val (car1 cdr1) cdr1)
      (else (report-expval-extractor-error 'pair val)))))

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
                 (set! exp exp1)
                 (set! env (init-env))
                 (value-of/k)))))

(define exp 'uninitialized)
(define env 'uninitialized)

; apply-procedure: proc x val -> finalanswer
(define apply-procedure/k
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (set! exp body)
                 (set! env (extend-env-let vars vals saved-env))
                 (value-of/k)))))

(define value-of/k
  (lambda ()
    (cases tfexp exp
      (simple-exp->exp (simple)
                       (value-of-simple-exp simple env))
      (cps-let-exp (vars rhs body)
               (let ((vals (map (lambda (x) (value-of-simple-exp x env)) rhs)))
                 (set! exp body)
                 (set! env (extend-env-let vars vals env))
                 (value-of/k)))
      (cps-letrec-exp (p-names b-varss p-bodies letrec-body)
                  (set! exp letrec-body)
                  (set! env (extend-env-rec* p-names b-varss p-bodies env))
                  (value-of/k))
      (cps-if-exp (simple1 body1 body2)
              (if (expval->bool (value-of-simple-exp simple1 env))
                  (begin (set! exp body1)
                         (value-of/k))
                  (begin (set! exp body2)
                         (value-of/k))))
      (cps-call-exp (rator rands)
                (let ((rator-proc (expval->proc (value-of-simple-exp rator env)))
                      (rand-vals (map (lambda (simple) (value-of-simple-exp simple env)) rands)))
                  (apply-procedure/k rator-proc rand-vals))))))
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
      (cps-mul-exp (exp1 exp2)
                   (let ((val1 (value-of-simple-exp exp1 env))
                         (val2 (value-of-simple-exp exp2 env)))
                     (num-val (* (expval->num val1)
                                 (expval->num val2)))))
      (cps-zero?-exp (exp1)
                     (let ((val1 (value-of-simple-exp exp1 env)))
                       (if (= (expval->num val1) 0)
                           (bool-val #t)
                           (bool-val #f))))
      (cps-proc-exp (vars body)
                    (proc-val (procedure vars body env)))
      (cons-exp (exp1 exp2)
                (pair-val (value-of-simple-exp exp1 env)
                          (value-of-simple-exp exp2 env)))
      (car-exp (exp1)
               (expval->car (value-of-simple-exp exp1 env)))
      (cdr-exp (exp1)
               (expval->cdr (value-of-simple-exp exp1 env)))
      (emptylist-exp ()
                      (emptylist-val))
      (list-exp (exps)
                (list-val (map (lambda (x) (value-of-simple-exp x env)) exps)))
      (null-exp (exp1)
                (cases expval (value-of-simple-exp exp1 env)
                  (emptylist-val () (bool-val #t))
                  (else (bool-val #f))))
      (equal-exp (exp1 exp2)
                 (if (equal? (value-of-simple-exp exp1 env) (value-of-simple-exp exp2 env))
                     (bool-val #t)
                     (bool-val #f)))
      (append-exp (exp1 exp2)
                  (append-val (value-of-simple-exp exp1 env)
                              (value-of-simple-exp exp2 env)))
      (pair?-exp (exp1)
                 (cases expval (value-of-simple-exp exp1 env)
                   (pair-val (car1 cdr1) (bool-val #t))
                   (else (bool-val #f))))
      (less-exp (exp1 exp2)
                (bool-val (< (expval->num (value-of-simple-exp exp1 env))
                             (expval->num (value-of-simple-exp exp2 env))))))))
