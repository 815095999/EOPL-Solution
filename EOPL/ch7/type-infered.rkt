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
      (tvar-type (serial-number)
                 (string->symbol
                  (string-append
                   "ty"
                   (number->string serial-number)))))))

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
               (an-answer (apply-tenv tenv var)
                          subst))
      (let-exp (var exp1 body)
               (cases answer (type-of exp1 tenv subst)
                 (an-answer (exp1-type subst)
                            (type-of body
                                     (extend-tenv var exp1-type tenv)
                                     subst))))
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
                                     (type-of letrec-body
                                              tenv-for-letrec-body
                                              subst)))))))
      )))


