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
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)
    (type ("%tvar-type" number) tvar-type)
    (optional-type ("?") no-type)
    (optional-type (type) a-type)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

; ------------------------------------------------------------------------------
; Errors and Test and Transfers
(define report-unification-failure
  (lambda (ty1 ty2 exp)
    (eopl:error 'unification-error "~s and ~s not match in exp :~s" ty1 ty2 exp)))
(define report-no-occurrence-violation
  (lambda (ty1 ty2 exp)
    (eopl:error 'no-occurrence-violation "~s occur in ~s in exp : ~s" ty1 ty2 exp)))
(define tvar-type?
  (lambda (ty)
    (cases type ty
      (tvar-type (serial-number) #t)
      (else #f))))
(define proc-type?
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) #t)
      (else #f))))
(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) arg-type)
      (else (eopl:error 'proc-type->arg-type "not a proc-type: ~s" ty)))))
(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-type result-type) result-type)
      (else (eopl:error 'proc-type->result-type "not a proc-type: ~s" ty)))))

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
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
                 (proc-type (apply-subst-to-type t1 subst)
                            (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
                 (let ((tmp (assoc ty subst)))
                   (if tmp
                       (cdr tmp)
                       ty))))))

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
    (let ((ty1 (if (tvar-type? ty1)
                   (apply-subst-to-type ty1 subst)
                   ty1))
          (ty2 (if (tvar-type? ty2)
                   (apply-subst-to-type ty2 subst)
                   ty2)))
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
        (else (report-unification-failure ty1 ty2 exp))))))
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
                 (and (no-occurrence? tvar arg-type)
                      (no-occurrence? tvar result-type)))
      (tvar-type (serial-number) (not (equal? tvar ty))))))