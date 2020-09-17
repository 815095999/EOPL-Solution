#lang eopl
; ------------------------------------------------------
; grammer
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("less?" "(" expression "," expression ")") less?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression ) "in" expression) let-exp)
    (expression ("proc" "(" (arbno identifier ",") ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("%lexref" number number) nameless-var-exp)
    (expression ("%let" (arbno expression) "in" expression) nameless-let-exp)
    (expression ("%lexproc" expression) nameless-proc-exp)
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)
(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

; ------------------------------------------------------
; senv

; empty-env: () -> senv
(define empty-senv
  (lambda ()
    '()))

; extend-env: (list-of var) x senv -> senv
(define extend-senv
  (lambda (vars senv)
    (cons vars senv)))

; apply-env: senv x var -> lexaddr
(define apply-senv
  (lambda (senv var)
    (define search-inner
      (lambda (var lst num)
        (if (equal? var (car lst))
            num
            (search-inner var (cdr lst) (+ num 1)))))
    (define search 
      (lambda (var env num)
        (cond ((null? env) (report-unbound-var var))
              ((memq var (car env))
               (cons num (search-inner var (car env) 0)))
              (else (search var (cdr env) (+ num 1))))))
    (search var senv 0)))

; init-senv: () -> senv
(define init-senv
  (lambda ()
    (extend-senv '(i v x) (empty-senv))))
(define report-unbound-var
  (lambda (var)
    (eopl:error "unbound-var ~s" var)))

; ------------------------------------------------------
; nameless-env

; nameless-environment?: schemeval -> bool
(define nameless-environment?
  (lambda (x)
    ((list-of (list-of expval?)) x)))

; empty-nameless-env: () -> nameless-env
(define empty-nameless-env
  (lambda () '()))

; extend-nameless-env: listof(expval) x nameless-env -> nameless-env
(define extend-nameless-env
  (lambda (vars nameless-env)
    (cons vars nameless-env)))

; apply-nameless-env: nameless-env x lexaddr -> expval
(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref (list-ref nameless-env (car n))
              (cdr n))))

; init-nameless-env: () -> nameless-env
(define init-nameless-env
  (lambda ()
    (list (map num-val '(1 2 4)))))
; ------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-nameless-env nameless-environment?)))

; apply-procedure: proc x expval -> expval
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (body nameless-env)
                 (value-of body (extend-nameless-env vals nameless-env))))))

; ------------------------------------------------------
; expval

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))

;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
           variant value)))


; ------------------------------------------------------
; value-of: nameless-exp x nameless-env -> expval
(define value-of
  (lambda (exp nameless-env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (diff-exp (exp1 exp2)
                (let ((val1 (value-of exp1 nameless-env))
                      (val2 (value-of exp2 nameless-env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                    (num-val (- num1 num2)))))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 nameless-env)))
                   (let ((num1 (expval->num val1)))
                     (bool-val (zero? num1)))))
      (if-exp (exp1 exp2 exp3)
              (let ((val1 (value-of exp1 nameless-env)))
                (if (expval->bool val1)
                    (value-of exp2 nameless-env)
                    (value-of exp3 nameless-env))))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator nameless-env))
                                 (map (lambda (rand) (value-of rand nameless-env)) rands)))
      (nameless-var-exp (car1 cdr1)
                        (apply-nameless-env nameless-env (cons car1 cdr1)))
      (nameless-let-exp (exps body)
                        (let ((vals (map (lambda (exp1) (value-of exp1 nameless-env)) exps)))
                          (value-of body (extend-nameless-env vals nameless-env))))
      (nameless-proc-exp (body)
                         (proc-val (procedure body nameless-env)))
      (else (report-invalid-translation-expression exp))
      )))

; ------------------------------------------------------
; translator
; translation-of: exp x senv -> nameless-exp
(define translation-of
  (lambda (exp senv)
    (cases expression exp
      (const-exp (num) (const-exp num))
      (diff-exp (exp1 exp2)
                (diff-exp (translation-of exp1 senv)
                          (translation-of exp2 senv)))
      (zero?-exp (exp1)
                 (zero?-exp (translation-of exp1 senv)))
      (if-exp (exp1 exp2 exp3)
              (if-exp (translation-of exp1 senv)
                      (translation-of exp2 senv)
                      (translation-of exp3 senv)))
      (var-exp (var)
               (let ((lex (apply-senv senv var)))
                 (nameless-var-exp (car lex) (cdr lex))))
      (let-exp (vars exps body)
               (nameless-let-exp (map (lambda (exp1) (translation-of exp1 senv)) exps)
                                 (translation-of body (extend-senv vars senv))))
      (proc-exp (vars body)
                (nameless-proc-exp (translation-of body (extend-senv vars senv))))
      (call-exp (rator rand)
                (call-exp (translation-of rator senv)
                          (translation-of rand senv)))
      (else (report-invalid-source-expression exp))
      )))

(define report-invalid-source-expression
  (lambda (exp)
    (eopl:error "invalid source expression ~s" exp)))

(define report-invalid-translation-expression
  (lambda (exp)
    (eopl:error "invalid translation expression ~s" exp)))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp) (value-of exp (init-nameless-env))))))

; translation-of-program: program -> nameless-program
(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program (translation-of exp1 (init-senv)))))))
(define run
  (lambda (string)
    (value-of-program
     (translation-of-program
      (scan&parse string)))))
(run "let x = 30 in let x = -(x,1)
          y = -(x,2)
          in -(x, y)")