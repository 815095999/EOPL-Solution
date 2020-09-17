#lang eopl
; 同样有两种方法，一种是即时生成procedure，另一种是用vector放一个procedure，这里采用第二种
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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("%lexref" number) nameless-var-exp)
    (expression ("%let" expression "in" expression) nameless-let-exp)
    (expression ("%lexproc" expression) nameless-proc-exp)
    (expression ("cond" (arbno expression "==>" expression) "end") cond-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("unpack" (arbno identifier) "=" expression "in" expression) unpack-exp)
    (expression ("%unpack" expression "in" expression) nameless-unpack-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    (expression ("%letrec" expression "in" expression) nameless-letrec-exp)
    (expression ("%lecvar" number) nameless-letrec-var-exp)
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

; extend-senv: var x senv -> senv
(define extend-senv
  (lambda (var senv)
    (cons var senv)))
(define extend-letrec-senv
  (lambda (var senv)
    (cons (cons 'letrec var)
          senv)))

; extend-senv*: (list-of var) x senv -> senv
(define extend-senv*
  (lambda (vars senv)
    (if (null? vars)
        senv
        (extend-senv* (cdr vars)
                      (cons (car vars) senv)))))

; apply-env: senv x var -> lexaddr
(define apply-senv
  (lambda (senv var)
    (cond ((null? senv) (report-unbound-var var))
          ((equal? var (car senv)) 0)
          ((and (pair? (car senv))
                (equal? var (cdar senv))) 0)
          (else (+ 1 (apply-senv (cdr senv) var))))))
;letrec-var?: var x senv -> bool
(define letrec-var?
  (lambda (var senv)
    (cond ((null? senv) #f)
          ((and (pair? (car senv))
                (equal? var (cdar senv)))
           #t)
          (else (letrec-var? var (cdr senv))))))

; translation-of-program: program -> nameless-program
(define translation-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (a-program (translation-of exp1 (init-senv)))))))

; init-senv: () -> senv
(define init-senv
  (lambda ()
    (extend-senv 'i
                 (extend-senv 'v
                              (extend-senv 'x (empty-senv))))))
(define report-unbound-var
  (lambda (var)
    (eopl:error "unbound-var ~s" var)))

; ------------------------------------------------------
; nameless-env

(define expval-or-vector?
  (lambda (x)
    (or (expval? x)
        (vector? x))))
; nameless-environment?: schemeval -> bool
(define nameless-environment?
  (lambda (x)
    ((list-of expval-or-vector?) x)))

; empty-nameless-env: () -> nameless-env
(define empty-nameless-env
  (lambda () '()))

; extend-nameless-env*: expval x nameless-env -> nameless-env
(define extend-nameless-env*
  (lambda (lst nameless-env)
    (cases expval lst
      (pair-val (car1 cdr1)
                (extend-nameless-env* cdr1
                                      (extend-nameless-env car1 nameless-env)))
      (emptylist () nameless-env)
      (else (eopl:error "unpack type error ~s" lst)))))

; extend-nameless-env: expval x nameless-env -> nameless-env
(define extend-nameless-env
  (lambda (var nameless-env)
    (cons var nameless-env)))

; apply-nameless-env: nameless-env x lexaddr -> expval
(define apply-nameless-env
  (lambda (nameless-env n)
    (list-ref nameless-env n)))

; init-nameless-env: () -> nameless-env
(define init-nameless-env
  (lambda ()
    (map num-val (list 1 2 4))))
; ------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure
   (body expression?)
   (saved-nameless-env nameless-environment?)))

; apply-procedure: proc x expval -> expval
(define apply-procedure
  (lambda (proc1 val)
    (cases proc proc1
      (procedure (body nameless-env)
                 (value-of body (extend-nameless-env val nameless-env))))))

; ------------------------------------------------------
; expval

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (pair-val
   (car1 expval?)
   (cdr1 expval?))
  (emptylist))

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

;; expval->car: pairval -> expval
(define expval->car
  (lambda v
    (cases expval v
      (pair-val (car1 cdr1) car1)
      (else (expval-extractor-error 'car v)))))

;; expval->cdr: pairval -> expval
(define expval->cdr
  (lambda v
    (cases expval v
      (pair-val (car1 cdr1) cdr1)
      (else (expval-extractor-error 'cdr v)))))

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
      (call-exp (rator rand)
                (apply-procedure (expval->proc (value-of rator nameless-env))
                                 (value-of rand nameless-env)))
      (nameless-var-exp (n)
                        (apply-nameless-env nameless-env n))
      (nameless-letrec-var-exp (n)
                               (vector-ref (apply-nameless-env nameless-env n) 0))
      (nameless-let-exp (exp1 body)
                        (let ((val (value-of exp1 nameless-env)))
                          (value-of body (extend-nameless-env val nameless-env))))
      (nameless-proc-exp (body)
                         (proc-val (procedure body nameless-env)))
      (cond-exp (conds acts)
                (cond-val conds acts nameless-env))
      (cons-exp (car1 cdr1)
                (pair-val (value-of car1 nameless-env)
                          (value-of cdr1 nameless-env)))
      (nameless-unpack-exp (expression body)
                           (value-of body
                                     (extend-nameless-env* (value-of expression nameless-env)
                                                           nameless-env)))
      (emptylist-exp () (emptylist))
      (nameless-letrec-exp (exp1 body)
                           (letrec ((vec (make-vector 1))
                                    (new-env (extend-nameless-env vec nameless-env)))
                             (vector-set! vec 0
                                          (proc-val (procedure exp1 new-env)))
                             (value-of body new-env)))
      (else (report-invalid-translation-expression exp))
      )))

; cond-val: conds x acts x nameless-env -> expval
(define cond-val
  (lambda (conds acts nameless-env)
    (cond ((null? conds)
           (eopl:error "no condition to enter"))
          ((expval->bool (value-of (car conds) nameless-env))
           (value-of (car acts) nameless-env))
          (else (cond-val (cdr conds)
                          (cdr acts)
                          nameless-env)))))
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
               (if (letrec-var? var senv)
                   (nameless-letrec-var-exp (apply-senv senv var))
                   (nameless-var-exp (apply-senv senv var))))
      (let-exp (var exp1 body)
               (nameless-let-exp (translation-of exp1 senv)
                                 (translation-of body (extend-senv var senv))))
      (proc-exp (var body)
                (nameless-proc-exp (translation-of body (extend-senv var senv))))
      (call-exp (rator rand)
                (call-exp (translation-of rator senv)
                          (translation-of rand senv)))
      (cond-exp (conds acts)
                (cond-exp (map (lambda (exp1) (translation-of exp1 senv)) conds)
                          (map (lambda (exp1) (translation-of exp1 senv)) acts)))
      (cons-exp (car1 cdr1)
                (cons-exp (translation-of car1 senv)
                          (translation-of cdr1 senv)))
      (unpack-exp (vars exp1 body)
                  (nameless-unpack-exp (translation-of exp1 senv)
                                       (translation-of body (extend-senv* vars senv))))
      (letrec-exp (func var exp1 body)
                  (letrec ((func-env (extend-letrec-senv func senv))
                           (var-env (extend-senv var func-env)))
                    (nameless-letrec-exp (translation-of exp1 var-env)
                                         (translation-of body func-env))))
      (emptylist-exp () (emptylist-exp))
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
(define run
  (lambda (string)
    (value-of-program
     (translation-of-program
      (scan&parse string)))))

(run "letrec
      func(x) =
       if zero?(x) then
          1
      else
         -((func -(x, 1)), -(0, x))
      in (func 1)")