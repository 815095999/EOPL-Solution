#lang eopl

; ex3.26 : 利用free-variable来筛选
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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
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
  (bool-val (bool boolean?))
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
(define extract-free-variable
  (lambda (frees env)
    (cases environment env
      (empty-env () (empty-env))
      (extend-env (var val env1)
                  (if (memq var frees)
                      (extend-env var val (extract-free-variable frees env1))
                      (extract-free-variable frees env1))))))
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
      (let-exp (var exp body)
               (let ((env1 (extend-env var (value-of exp env) env)))
                 (value-of body env1)))
      (proc-exp (vars body)
                (proc-val (procedure vars
                                     body
                                     (extract-free-variable (free-variable body vars) env))))
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
; ------------------------------------------------------------------------------
(define free-variable
  (lambda (exp bound)
    (cases expression exp
      (const-exp (num) '())
      (plus-exp (exp1 exp2)
                (append (free-variable exp1 bound)
                        (free-variable exp2 bound)))
      (diff-exp (exp1 exp2)
                (append (free-variable exp1 bound)
                        (free-variable exp2 bound)))
      (mul-exp (exp1 exp2)
               (append (free-variable exp1 bound)
                       (free-variable exp2 bound)))
      (div-exp (exp1 exp2)
               (append (free-variable exp1 bound)
                       (free-variable exp2 bound)))
      (if-exp (exp1 exp2 exp3)
              (append (free-variable exp1 bound)
                      (free-variable exp2 bound)
                      (free-variable exp3 bound)))
      (var-exp (var)
               (if (memq var bound)
                   '()
                   (list var)))
      (minus-exp (exp1)
                 (free-variable exp1 bound))
      (let-exp (var exp body)
               (append (free-variable exp bound)
                       (free-variable body (cons var bound))))
      (proc-exp (vars body)
                (free-variable body (append vars bound)))
      (call-exp (rator rands)
                (append (free-variable rator bound)
                        (free-variable-list rands bound)))
      (zero?-exp (exp1)
                 (free-variable exp1 bound))
      (greater?-exp (exp1 exp2)
                    (append (free-variable exp1 bound)
                            (free-variable exp2 bound)))
      (less?-exp (exp1 exp2)
                 (append (free-variable exp1 bound)
                         (free-variable exp2 bound)))
      (equal?-exp (exp1 exp2)
                  (append (free-variable exp1 bound)
                         (free-variable exp2 bound)))
      )))
(define free-variable-list
  (lambda (lst bound)
    (if (null? lst)
        '()
        (append (free-variable (car lst) bound)
                (free-variable-list (cdr lst) bound)))))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))

(define run-free
  (lambda (pgm)
    (cases program pgm
           (a-program (exp1)
                      (free-variable exp1 '())))))
(define run-free-v
  (lambda (prog)
    (run-free (scan&parse prog))))

; (display (run-free-v "proc(x) -(x, y)"))
;;-> (y)

; (run "proc(x) -(x, 1)")
;(run "(proc(x) -(x,1)  30)")
;(run "let f = proc (x) -(x,1) in (f 30)")
;(run "(proc(f)(f 30)  proc(x)-(x,1))")
(run-free-v "let makerec = proc (f)
        let d = proc (x)
          proc (z) ((f (x x)) z)
        in proc (n) ((f (d d)) n)
     in let maketimes4 = proc (f) proc (x)
          if zero?(x)
             then 0
          else -((f -(x,1)), z)
      in let times4 = (makerec maketimes4) in (times4 z)")
;; ==> (z z)

;(run "proc(x) -(x, 1)")
;(run "(proc(x) -(x,1)  30)")
;(run "let f = proc (x) -(x,1) in (f 30)")
;(run "(proc(f)(f 30)  proc(x)-(x,1))")