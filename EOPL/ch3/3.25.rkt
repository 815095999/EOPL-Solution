#lang eopl

; ex3.25 : 注意到调用(maketimes (d d) n)会规约到(maketimes (d d) -(n,1))即可
; ------------------------------------------------------------------------------
; Environments

; See: exercise 2.5

; identifier: schemeval -> bool
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
; value: schemeval -> bool
(define value?
  (lambda (x)
    #t))

(define-datatype environment environment?
  (empty-env)
  (extend-env (saved-var identifier?)
              (saved-val value?)
              (saved-env environment?)))

; apply-env environment x identifier -> schemeval
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env () (report-no-binding-found search-var))
      (extend-env (var val env1)
                  (if (equal? var search-var)
                      val
                      (apply-env env1 search-var))))))

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
    (expression ("+" "(" expression "," expression ")") plus-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("*" "(" expression "," expression ")") mul-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("equal?" "(" expression "," expression ")") equal?-exp)
    (expression ("greater?" "(" expression "," expression ")") greater?-exp)
    (expression ("less?" "(" expression "," expression ")" ) less?-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("list" "(" (separated-list expression ",") ")" ) list-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("print" "(" expression ")") print-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("let*" (arbno identifier "=" expression) "in" expression) let*-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
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
  (bool-val (bool boolean?))
  (emptylist-val)
  (proc-val (proc proc?)))

; expval->num: expval -> num
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
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
;expval->car: expval -> expval
(define expval->car
  (lambda (val)
    (cases expval val
      (pair-val (car cdr) car)
      (else (report-expval-extractor-error 'pair val)))))
;expval->cdr: expval -> expval
(define expval->cdr
  (lambda (val)
    (cases expval val
      (pair-val (car cdr) cdr)
      (else (report-expval-extractor-error 'pair val)))))
(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

; ------------------------------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?)))
; extend-env*: listof(identifier) x listof(vals) x env -> env
(define extend-env*
  (lambda (vars vals env)
    (cond ((= (length vars) (length vals))
           (cond ((null? vars) env)
                 (else (extend-env* (cdr vars)
                                    (cdr vals)
                                    (extend-env (car vars) (car vals) env)))))
          (else (eopl:error 'extend-env* "not enough arguments! ~% expected: ~s detected: ~s" (length vars) (length vals))))))
; apply-procedure: proc x val -> val
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of body (extend-env* vars vals saved-env))))))


; ------------------------------------------------------------------------------
; Interpreter

; run: string -> val
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program: program -> val
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of exp1 (init-env))))))
; list-val: listof(val) -> val
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
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
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
      (unpack-exp (vars exp1 body)
                  (let ((env1 (extend-env-unpack vars (value-of exp1 env) env)))
                    (value-of body env1)))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator env))
                                 (map (lambda (rand) (value-of rand env)) rands)))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (bool-val (zero? num1)))))
      (greater?-exp (exp1 exp2)
                    (letrec ((val1 (value-of exp1 env))
                             (val2 (value-of exp2 env))
                             (num1 (expval->num val1))
                             (num2 (expval->num val2)))
                      (bool-val (> num1 num2))))
      (less?-exp (exp1 exp2)
                 (letrec ((val1 (value-of exp1 env))
                          (val2 (value-of exp2 env))
                          (num1 (expval->num val1))
                          (num2 (expval->num val2)))
                   (bool-val (< num1 num2))))
      (equal?-exp (exp1 exp2)
                  (letrec ((val1 (value-of exp1 env))
                           (val2 (value-of exp2 env))
                           (num1 (expval->num val1))
                           (num2 (expval->num val2)))
                    (bool-val (= num1 num2))))
      )))
(define extend-env-unpack
  (lambda (vars lst env)
    (if (null? vars)
        env
        (cases expval lst
          (pair-val (fir sec)
                    (extend-env-unpack (cdr vars)
                                       sec
                                       (extend-env (car vars)
                                                   fir
                                                   env)))
          (else (report-expval-extractor-error 'pair 'num))))))
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
          ((expval->bool (value-of (car conds) env))
           (value-of (car acts) env))
          (else (cond-val (cdr conds) (cdr acts) env)))))

; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))
(display (run "let makerec = proc (f) let d = proc (x) proc (z) ((f (x x)) z) in proc (n) ((f (d d)) n) in let maketimes4 = proc (f) proc (x) if zero?(x) then 0 else -((f -(x,1)), -4)

in let times4 = (makerec maketimes4)

in (times4 3)"))