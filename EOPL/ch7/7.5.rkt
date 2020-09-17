#lang eopl

; procedural representation style
; ------------------------------------------------------------------------------
; tenvironments
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var identifier?)
               (val type?)
               (tenv tenvironment?)))
(define apply-tenv
  (lambda (tenv search-var)
    (cases tenvironment tenv
      (empty-tenv ()
                  (report-no-binding-found search-var))
      (extend-tenv (saved-var saved-val saved-tenv)
                   (if (equal? saved-var search-var)
                       saved-val
                       (apply-tenv saved-tenv search-var))))))
(define extend-tenv*
  (lambda (vars vals tenv)
    (if (null? vals)
        tenv
        (extend-tenv (car vars)
                     (car vals)
                     (extend-tenv* (cdr vars) (cdr vals) tenv)))))
(define extend-tenv-rec
  (lambda (p-names b-var-typess p-result-types tenv)
    (if (null? p-names)
        tenv
        (extend-tenv (car p-names)
                     (proc-type (car b-var-typess)
                                (car p-result-types))
                     (extend-tenv-rec (cdr p-names)
                                     (cdr b-var-typess)
                                     (cdr p-result-types)
                                     tenv)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-tenv "No binding for ~s" search-var)))

(define init-tenv
  (lambda ()
    (extend-tenv 'i (int-type)
                 (extend-tenv 'v (bool-type)
                              (extend-tenv 'x (int-type)
                                           (empty-tenv))))))
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
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("proc" "(" (arbno identifier ":" type) ")" expression) proc-exp)
    (expression ("letrec" (arbno type identifier "(" (arbno identifier ":" type) ")" "=" expression) "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (arbno type) "->" type ")") proc-type)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

; ------------------------------------------------------------------------------
; the checker

; check-equal-type! : type x type x exp -> unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp)
        #t)))

; report-unequal-types : type x type x exp -> unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
                "Types didn't match: ~s != ~a in ~% ~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

; type-to-external-form : type -> list
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-types result-type)
                 (append (map type-to-external-form arg-types)
                         (list '->
                               (type-to-external-form result-type)))))))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'rator-type-error "rator ~s has type ~s" rator rator-type)))

; ------------------------------------------------------------------------------

; type-of-program : program -> type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1) (type-of exp1 (init-tenv))))))

; run: string -> finalanswer
(define run
  (lambda (string)
    (type-to-external-form (type-of-program (scan&parse string)))))

; type-of : exp x tenv -> type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ((ty1 (type-of exp1 tenv))
                      (ty2 (type-of exp2 tenv)))
                  (check-equal-type! ty1 (int-type) exp1)
                  (check-equal-type! ty2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ((ty1 (type-of exp1 tenv)))
                   (check-equal-type! ty1 (int-type) exp1)
                   (bool-type)))
      (if-exp (exp1 exp2 exp3)
              (let ((ty1 (type-of exp1 tenv))
                    (ty2 (type-of exp2 tenv))
                    (ty3 (type-of exp3 tenv)))
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))
      (let-exp (vars exps body)
               (let ((exp-types (map (lambda (x) (type-of x tenv)) exps)))
                 (type-of body (extend-tenv* vars exp-types tenv))))
      (proc-exp (vars var-types body)
                (let ((result-type (type-of body
                                            (extend-tenv* vars var-types tenv))))
                  (proc-type var-types result-type)))
      (call-exp (rator rands)
                (let ((rator-type (type-of rator tenv))
                      (rand-types (map (lambda (x) (type-of x tenv)) rands)))
                  (cases type rator-type
                    (proc-type (arg-types result-type)
                               (begin (check-equal-type! arg-types rand-types rands)
                                      result-type))
                    (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp (p-result-types p-names b-varss b-var-typess p-bodies letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv-rec p-names b-var-typess p-result-types tenv)))
                    (let ((p-body-types
                           (types-of-p-bodies b-varss b-var-typess p-bodies tenv-for-letrec-body)))
                      (check-equal-type! p-body-types p-result-types p-bodies)
                      (type-of letrec-body tenv-for-letrec-body))))
      )))

(define types-of-p-bodies
  (lambda (b-varss b-var-typess p-bodies tenv)
    (if (null? b-varss)
        '()
        (cons (type-of (car p-bodies)
                       (extend-tenv* (car b-varss)
                                    (car b-var-typess)
                                    tenv))
              (types-of-p-bodies (cdr b-varss)
                                (cdr b-var-typess)
                                (cdr p-bodies)
                                tenv)))))

(run "letrec int double(x : int) = -(x,-(0,x))
             bool one?(x : int) = zero?(-(x,1))
             int sum(x : int y : int) = -(x,-(0,y))
             in (sum 3 (double 5))")