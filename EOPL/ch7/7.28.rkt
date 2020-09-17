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
               (tenv tenvironment?))
  (extend-tenv-delayed (var identifier?)
                       (val procedure?)
                       (tenv tenvironment?)))

(define apply-tenv
  (lambda (tenv search-var)
    (cases tenvironment tenv
      (empty-tenv ()
                  (report-no-binding-found search-var))
      (extend-tenv (saved-var saved-val saved-tenv)
                   (if (equal? saved-var search-var)
                       saved-val
                       (apply-tenv saved-tenv search-var)))
      (extend-tenv-delayed (saved-var saved-val saved-tenv)
                           (if (equal? saved-var search-var)
                               saved-val
                               (apply-tenv saved-tenv search-var))))))

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
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("proc" "(" identifier ":" optional-type ")" expression) proc-exp)
    (expression
     ("letrec" optional-type identifier "(" identifier ":" optional-type ")"
               "=" expression "in" expression) letrec-exp)
    (expression ("list" "(" expression (arbno  "," expression) ")") list-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("null?" "(" expression ")") null-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("newpair" "(" expression "," expression ")") pair-exp)
    (expression ("unpair" identifier identifier "=" expression "in" expression) unpair-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)
    (type ("%tvar-type" number) tvar-type)
    (type ("listof" type) list-type)
    (type ("pair" type "*" type) pair-type)
    (optional-type ("?") no-type)
    (optional-type (type) a-type)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

; ------------------------------------------------------------------------------
; Errors 
(define report-unification-failure
  (lambda (ty1 ty2 exp)
    (eopl:error 'unification-error "~s and ~s not match in exp :~s" ty1 ty2 exp)))
(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error 'no-occurrence-violation "~s occur in ~s in exp : ~s" ty1 ty2 exp)))


; ------------------------------------------------------------------------------
; Data Structures
; tvar-type? : type -> bool
(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type (serial-number) #t)
      (else #f))))

; proc-type : type -> bool
(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) #t)
      (else #f))))

; proc-type->arg-type : type -> type
(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type "not a proc-type: ~s" ty)))))

; proc-type->result-type : type -> type
(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-type "not a proc-type: ~s" ty)))))

; pair-type : type -> bool
(define pair-type?
  (lambda (ty)
    (cases type ty
      (pair-type (arg-type result-type) #t)
      (else #f))))

; pair-type->fir-type : type -> type
(define pair-type->fir-type
  (lambda (ty)
    (cases type ty
      (pair-type (arg-type result-type) arg-type)
      (else (eopl:error 'pair-type->fir-type "not a pair-type: ~s" ty)))))

; pair-type->sec-type : type -> type
(define pair-type->sec-type
  (lambda (ty)
    (cases type ty
      (pair-type (arg-type result-type) result-type)
      (else (eopl:error 'pair-type->sec-type "not a pair-type: ~s" ty)))))

; list-type? : type-> bool
(define list-type?
  (lambda (ty)
    (cases type ty
      (list-type (ty1) #t)
      (else #f))))

; list-type->type : type -> type
(define list-type->type
  (lambda (ty)
    (cases type ty
      (list-type (ty1) ty1)
      (else (eopl:error 'list-type->type "not a list-type: ~s" ty)))))

; optype->type: Optionaltype -> type
(define otype->type
  (lambda (otype)
    (cases optional-type otype
      (no-type () (fresh-tvar-type))
      (a-type (ty) ty))))

; fresh-tvar-type : () -> type
(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))

(define substitution? (lambda (x) (or (null? x) (pair? x))))
(define-datatype answer answer?
  (an-answer
   (ty type?)
   (subst substitution?)))

; ------------------------------------------------------------------------------
; TvarTypeSym

; canonical-form : sexp -> sexp
(define canonical-form
  (lambda (sexp)
    (apply-subst-to-sexp (canonical-subst sexp) sexp)))
; equal-up-to-gensyms? : sexp x sexp -> bool
(define equal-up-to-gensyms?
  (lambda (sexp1 sexp2)
    (equal?
     (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
     (apply-subst-to-sexp (canonical-subst sexp2) sexp2))))

; canonical-subst: sexp -> a-list
(define canonical-subst
  (lambda (sexp)
    ; loop : s-exp x a-list -> a-list 
    (let loop ((sexp sexp) (table '()))
      (cond
        ((null? sexp) table)
        ((pair? sexp)
         (loop (cdr sexp) (loop (car sexp) table)))
        ((tvar-type-sym? sexp)
         (cond
           ((assq sexp table) table)
           (else
            (cons (cons sexp (ctr->ty (length table)))
                  table))))
        (else table)))))
; tvar-type-sym? : sym -> bool
(define tvar-type-sym?
  (lambda (sym)
    (and (symbol? sym)
         (char-numeric? (car (reverse (symbol->list sym)))))))

; symbol->list : sym -> list
(define symbol->list
  (lambda (x)
    (string->list (symbol->string x))))

; apply-subst-to-sexp : a-list x s-exp -> s-exp
(define apply-subst-to-sexp
  (lambda (subst sexp)
    (cond ((null? sexp) sexp)
          ((tvar-type-sym? sexp)
           (cdr (assq sexp subst)))
          ((pair? sexp)
           (cons
            (apply-subst-to-sexp subst (car sexp))
            (apply-subst-to-sexp subst (cdr sexp))))
          (else sexp))))

; cty->ty : N -> sym
(define ctr->ty
  (lambda (n)
    (string->symbol
     (string-append "ty" (number->string n)))))



; ------------------------------------------------------------------------------
; Substitutions
; apply-one-subst: type x tvar x type -> type
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
                 (proc-type (apply-one-subst arg-type tvar ty1)
                            (apply-one-subst result-type tvar ty1)))
      (list-type (ty2)
                 (list-type (apply-one-subst ty2 tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0))
      (pair-type (ty3 ty4)
                 (pair-type (apply-one-subst ty3 tvar ty1)
                            (apply-one-subst ty4 tvar ty1))))))

; apply-subst-to-type
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type (apply-subst-to-type t1 subst)
                            (apply-subst-to-type t2 subst)))
      (list-type (t1)
                 (list-type (apply-subst-to-type t1 subst)))
      (tvar-type (sn)
                 (let ((tmp (assoc ty subst)))
                   (if tmp
                       (cdr tmp)
                       ty)))
      (pair-type (t1 t2)
                 (pair-type (apply-subst-to-type t1 subst)
                            (apply-subst-to-type t2 subst)))
      )))

; empty-subst: () -> subst
(define empty-subst (lambda () '()))

; extend-subst: subst x tvar x type -> subst
(define extend-subst
  (lambda (subst tvar ty)
    (cons
     (cons tvar ty)
     (map (lambda (p)
            (let ((oldlhs (car p))
                  (oldrhs (cdr p)))
              (cons oldlhs
                    (apply-one-subst oldrhs tvar ty))))
          subst))))

; unifier: type x type x subst x exp -> subst
(define unifier
  (lambda (ty1 ty2 subst exp)
    (let ((ty1 (apply-subst-to-type ty1 subst))
          (ty2 (apply-subst-to-type ty2 subst)))
      (cond
        ((equal? ty1 ty2) subst)
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
             (extend-subst subst ty1 ty2)
             (report-no-occurrence-violation ty1 ty2 exp)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
             (extend-subst subst ty2 ty1)
             (report-no-occurrence-violation ty2 ty1 exp)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (let ((subst (unifier (proc-type->arg-type ty1)
                               (proc-type->arg-type ty2)
                               subst exp)))
           (let ((subst (unifier (proc-type->result-type ty1)
                                 (proc-type->result-type ty2)
                                 subst exp)))
             subst)))
        ((and (list-type? ty1) (list-type? ty2))
         (unifier (list-type->type ty1)
                  (list-type->type ty2)
                  subst exp))
        ((and (pair-type? ty1) (pair-type? ty2))
         (let ((subst (unifier (pair-type->fir-type ty1)
                               (pair-type->fir-type ty2)
                               subst exp)))
           (let ((subst (unifier (pair-type->sec-type ty1)
                                 (pair-type->sec-type ty2)
                                 subst exp)))
             subst)))
        (else (report-unification-failure ty1 ty2 exp))))))
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
                 (and (no-occurrence? tvar arg-type)
                      (no-occurrence? tvar result-type)))
      (list-type (ty1)
                 (no-occurrence? tvar ty1))
      (tvar-type (serial-number) (not (equal? tvar ty)))
      (pair-type (arg-type result-type)
                 (and (no-occurrence? tvar arg-type)
                      (no-occurrence? tvar result-type)))
      )))


; ------------------------------------------------------------------------------
; type-infered interpreter

; type-to-external-form : type -> list
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type)
                 (list (type-to-external-form arg-type)
                       '->
                       (type-to-external-form result-type)))
      (list-type (ty1)
                 (list 'list-type
                       (type-to-external-form ty1)))
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "ty"
                   (number->string serial-number))))
      (pair-type (arg-type result-type)
                 (list 'pair
                       (type-to-external-form arg-type)
                       '*
                       (type-to-external-form result-type))))))

; type-of-program : program -> type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
                 (cases answer (type-of exp1 (init-tenv) (empty-subst))
                   (an-answer (ty subst)
                              (apply-subst-to-type ty subst)))))))
(define run
  (lambda (str)
    (canonical-form (type-to-external-form (type-of-program (scan&parse str))))))

; type-of : exp x tenv x subst -> answer
(define type-of
  (lambda (exp tenv subst)
    (cases expression exp
      (const-exp (num) (an-answer (int-type) subst))
      (zero?-exp (exp1)
                 (cases answer (type-of exp1 tenv subst)
                   (an-answer (ty1 subst1)
                              (let ((subst2
                                     (unifier ty1 (int-type) subst1 exp)))
                                (an-answer (bool-type) subst2)))))
      (diff-exp (exp1 exp2)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (ty1 subst1)
                             (let ((subst1
                                    (unifier ty1 (int-type) subst1 exp1)))
                               (cases answer (type-of exp2 tenv subst1)
                                 (an-answer (ty2 subst2)
                                            (let ((subst2
                                                   (unifier ty2 (int-type) subst2 exp2)))
                                              (an-answer (int-type) subst2))))))))
      (if-exp (exp1 exp2 exp3)
              (cases answer (type-of exp1 tenv subst)
                (an-answer (ty1 subst)
                           (let ((subst
                                  (unifier ty1 (bool-type) subst exp1)))
                             (cases answer (type-of exp2 tenv subst)
                               (an-answer (ty2 subst)
                                          (cases answer (type-of exp3 tenv subst)
                                            (an-answer (ty3 subst)
                                                       (let ((subst
                                                              (unifier ty2 ty3 subst exp)))
                                                         (an-answer ty2 subst))))))))))
      (var-exp (var)
               (let ((ty1 (apply-tenv tenv var)))
                 (if (type? ty1)
                     (an-answer ty1 subst)
                     (ty1 subst))))
      
      (let-exp (var exp1 body)
               (type-of exp1 tenv subst)
               (type-of body
                        (extend-tenv-delayed var (lambda (subst) (type-of exp1 tenv subst)) tenv)
                        subst))
      (proc-exp (var otype body)
                (let ((var-type (otype->type otype)))
                  (cases answer (type-of body
                                         (extend-tenv var var-type tenv)
                                         subst)
                    (an-answer (body-type subst)
                               (an-answer (proc-type var-type body-type)
                                          subst)))))
      (call-exp (rator rand)
                (let ((result-type (fresh-tvar-type)))
                  (cases answer (type-of rator tenv subst)
                    (an-answer (rator-type subst)
                               (cases answer (type-of rand tenv subst)
                                 (an-answer (rand-type subst)
                                            (let ((subst
                                                   (unifier rator-type
                                                            (proc-type rand-type result-type)
                                                            subst
                                                            exp)))
                                              (an-answer result-type subst))))))))
      (letrec-exp (p-result-otype p-name b-var b-var-otype p-body letrec-body)
                  (define check-proc
                    (lambda (subst)
                      (let ((p-result-type (otype->type p-result-otype))
                            (p-var-type (otype->type b-var-otype)))
                        (let ((tenv-for-letrec-body (extend-tenv p-name
                                                                 (proc-type p-var-type
                                                                            p-result-type)
                                                                 tenv)))
                          (cases answer (type-of p-body (extend-tenv b-var p-var-type
                                                                 tenv-for-letrec-body)
                                             subst)
                            (an-answer (p-body-type subst)
                                       (let ((subst
                                              (unifier p-body-type p-result-type subst p-body)))
                                         (an-answer (proc-type p-var-type
                                                               p-result-type)
                                                    subst))))))))
                  
                    (check-proc subst)
                    (type-of letrec-body
                             (extend-tenv-delayed p-name
                                                  check-proc
                                                  tenv)
                             subst))
      (emptylist-exp ()
                     (an-answer (list-type (fresh-tvar-type)) subst))
      (cons-exp (exp1 exp2)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (exp1-type subst)
                             (cases answer (type-of exp2 tenv subst)
                               (an-answer (exp2-type subst)
                                          (let ((subst
                                                  (unifier exp2-type
                                                           (list-type exp1-type)
                                                           subst exp)))
                                            (an-answer (list-type exp1-type)
                                                       subst)))))))
      (car-exp (exp1)
               (cases answer (type-of exp1 tenv subst)
                 (an-answer (exp1-type subst)
                            (let* ((ty2 (fresh-tvar-type))
                                   (subst
                                    (unifier exp1-type
                                             (list-type ty2)
                                             subst exp)))
                              (an-answer ty2 subst)))))
      (cdr-exp (exp1)
               (cases answer (type-of exp1 tenv subst)
                 (an-answer (exp1-type subst)
                            (let ((subst
                                   (unifier exp1-type
                                            (list-type (fresh-tvar-type))
                                            subst exp)))
                              (an-answer exp1-type subst)))))
      (list-exp (exp1 exps)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (exp1-type subst)
                             (if (null? exps)
                                 (an-answer (list-type exp1-type) subst)
                                 (cases answer (type-of (list-exp (car exps)
                                                                  (cdr exps))
                                                        tenv subst)
                                   (an-answer (exps-type subst)
                                              (let ((subst
                                                     (unifier exp1-type
                                                              (list-type->type exps-type)
                                                              subst exp)))
                                                (an-answer (exps-type) subst))))))))
      (null-exp (exp1)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (exp1-type subst)
                             (let ((subst
                                    (unifier exp1-type
                                             (list-type (fresh-tvar-type))
                                             subst exp)))
                               (an-answer (bool-type) subst)))))
      (pair-exp (exp1 exp2)
                (cases answer (type-of exp1 tenv subst)
                  (an-answer (exp1-type subst)
                             (cases answer (type-of exp2 tenv subst)
                               (an-answer (exp2-type subst)
                                          (an-answer (pair-type exp1-type exp2-type)
                                                     subst))))))
      (unpair-exp (var1 var2 exp1 body)
                  (cases answer (type-of exp1 tenv subst)
                    (an-answer (exp1-type subst)
                               (type-of body
                                        (extend-tenv var1
                                                     (pair-type->fir-type exp1-type)
                                                     (extend-tenv var2
                                                                  (pair-type->sec-type exp1-type)
                                                                  tenv))
                                        subst))))
      )))


(run "letrec ? map (f:?) =  letrec ? foo (x : ?) = if null?(x)
                                                    then emptylist
                                                    else cons((f car(x)), ((map f) cdr(x)))
                            in foo
      in letrec ? even (y : ?) = if zero?(y)
                                 then zero?(0)
                                 else if zero?(-(y,1)) then zero?(1) else (even -(y,2))
      in newpair(((map proc(x : int) -(x,1)) cons(3,cons(5,emptylist))), ((map even) cons(3,cons(5,emptylist))))")