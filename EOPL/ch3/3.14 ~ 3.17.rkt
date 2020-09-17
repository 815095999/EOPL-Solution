#lang eopl

; ------------------------------------------------------------------------------
; Environments

; See: exercise 2.5

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))

(define apply-env
  (lambda (initial-env search-var)
    (letrec ((loop (lambda (env)
                     (cond ((null? env)
                            (report-no-binding-found search-var initial-env))
                           ((and (pair? env) (pair? (car env)))
                            (let ((saved-var (caar env))
                                  (saved-val (cdar env))
                                  (saved-env (cdr env)))
                              (if (eqv? search-var saved-var)
                                  saved-val
                                  (loop saved-env))))
                           (else
                            (report-invalid-env initial-env))))))
      (loop initial-env))))

(define report-no-binding-found
  (lambda (search-var env)
    (eopl:error 'apply-env "No binding for ~s in ~s" search-var env)))

(define report-invalid-env
  (lambda (env)
    (eopl:error 'apply-env "Bad environment ~s" env)))

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
    (expression ("+" "(" expression "," expression ")") plus-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("if" bool-exp "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (bool-exp ("zero?" "(" expression ")") zero?-bool-exp)
    (bool-exp ("equal?" "(" expression "," expression ")") equal?-bool-exp)
    (bool-exp ("greater?" "(" expression "," expression ")") greater?-bool-exp)
    (bool-exp ("less?" "(" expression "," expression ")" ) less?-bool-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)
    (expression ("cond" (arbno bool-exp "==>" expression) "end") cond-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
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
  (pair-val (car expval?)
            (cdr expval?))
  (emptylist-val))
(define-datatype boolexpval boolexpval?
  (bool-val (bool boolean?)))
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
(define boolexpval->bool
  (lambda (val)
    (cases boolexpval val
      (bool-val (num) num))))
(define expval->car
  (lambda (val)
    (cases expval val
      (pair-val (car cdr) car)
      (else (report-expval-extractor-error 'pair 'val)))))
(define expval->cdr
  (lambda (val)
    (cases expval val
      (pair-val (car cdr) cdr)
      (else (report-expval-extractor-error 'pair 'val)))))
(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))


; ------------------------------------------------------------------------------
; Interpreter

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of exp1 (init-env))))))
(define list-val
  (lambda (lst)
    (cond ((null? lst) (emptylist-val))
          (else (pair-val (car lst)
                          (list-val (cdr lst)))))))
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (plus-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (+ num1 num2)))))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (mul-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (* num1 num2)))))
      (div-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (quotient num1 num2)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of-bool-exp exp1 env)))
          (if (boolexpval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))
      (var-exp (var)
        (apply-env env var))
      (minus-exp (exp1)
        (let ((val1 (value-of exp1 env)))
          (let ((num1 (expval->num val1)))
            (num-val (- num1)))))
      (emptylist-exp () (emptylist-val))
      (cons-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (pair-val val1 val2)))
      (car-exp (exp1)
               (expval->car (value-of exp1 env)))
      (cdr-exp (exp1)
               (expval->cdr (value-of exp1 env)))
      (list-exp (args)
                (list-val (map (lambda (exp) (value-of exp env))args)))
      (cond-exp (conds acts)
                (cond-val conds acts env))
      (print-exp (exp1)
                 (display (value-of exp1 env))
                 (newline)
                 (num-val 1))
      (let-exp (vars exps body)
        (let ((env1 (extend-env-let vars exps env env)))
          (value-of body env1)))
      (let*-exp (vars exps body)
        (let ((env1 (extend-env-let* vars exps env)))
          (value-of body env1)))
      )))
(define extend-env-let*
  (lambda (vars exps env)
    (if (null? vars)
        env
        (extend-env-let* (cdr vars)
                        (cdr exps)
                        (extend-env (car vars)
                                    (value-of (car exps) env)
                                    env)))))
(define extend-env-let
  (lambda (vars exps env ori_env)
    (if (null? vars)
        env
        (extend-env-let (cdr vars)
                        (cdr exps)
                        (extend-env (car vars)
                                    (value-of (car exps) ori_env)
                                    env)
                        ori_env))))
(define cond-val
  (lambda (conds acts env)
    (cond ((null? conds)
           (eopl:error 'cond-val "No conditions got into #t"))
          ((boolexpval->bool (value-of-bool-exp (car conds) env))
           (value-of (car acts) env))
          (else (cond-val (cdr conds) (cdr acts) env)))))
(define value-of-bool-exp
  (lambda (exp env)
    (cases bool-exp exp
      (zero?-bool-exp (exp1)
                      (let ((val1 (value-of exp1 env)))
                        (let ((num1 (expval->num val1)))
                          (bool-val (zero? num1)))))
      (greater?-bool-exp (exp1 exp2)
                         (letrec ((val1 (value-of exp1 env))
                                  (val2 (value-of exp2 env))
                                  (num1 (expval->num val1))
                                  (num2 (expval->num val2)))
                           (bool-val (> num1 num2))))
      (less?-bool-exp (exp1 exp2)
                      (letrec ((val1 (value-of exp1 env))
                               (val2 (value-of exp2 env))
                               (num1 (expval->num val1))
                               (num2 (expval->num val2)))
                        (bool-val (< num1 num2))))
      (equal?-bool-exp (exp1 exp2)
                       (letrec ((val1 (value-of exp1 env))
                                (val2 (value-of exp2 env))
                                (num1 (expval->num val1))
                                (num2 (expval->num val2)))
                         (bool-val (= num1 num2))))
      )))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))

