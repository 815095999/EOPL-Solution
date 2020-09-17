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
  (lambda (vars types tenv)
    (if (null? vars)
        tenv
        (extend-tenv (car vars)
                     (car types)
                     (extend-tenv* (cdr vars)
                                   (cdr types)
                                   tenv)))))
(define extend-tenv-rec
  (lambda (p-names p-var-typess p-result-types tenv)
    (if (null? p-names)
        tenv
        (extend-tenv (car p-names)
                     (proc-type (car p-var-typess)
                                (car p-result-types))
                     (extend-tenv-rec (cdr p-names)
                                      (cdr p-var-typess)
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
    (expression ("proc" "(" (arbno identifier ":" optional-type) ")" expression) proc-exp)
    (expression
     ("letrec" (arbno optional-type identifier "(" (arbno identifier ":" optional-type) ")"
                      "=" expression) "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (arbno type) "->" type ")") proc-type)
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
      (proc-type (arg-types result-type) #t)
      (else #f))))

; proc-type->arg-types : type -> listof(type)
(define proc-type->arg-types
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type) arg-types)
      (else (eopl:error 'proc-type->arg-types "not a proc-type: ~s" ty)))))

; proc-type->result-type : type -> type
(define proc-type->result-type
  (lambda (ty)
    (cases type ty
      (proc-type (arg-types result-type) result-type)
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
      (proc-type (arg-types result-type)
                 (proc-type (map (lambda (x) (apply-one-subst x tvar ty1)) arg-types)
                            (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
                 (if (equal? ty0 tvar) ty1 ty0)))))

; apply-subst-to-type
(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1s t2)
                 (proc-type (map (lambda (x) (apply-subst-to-type x subst)) t1s)
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
         (let loop ([ty1s (proc-type->arg-types ty1)]
                    [ty2s (proc-type->arg-types ty2)]
                    [subst subst])
           (if (= (length ty1s) (length ty2s))
               (if (null? ty1s)
                   (unifier (proc-type->result-type ty1)
                            (proc-type->result-type ty2)
                            subst exp)
                   (loop (cdr ty1s)
                         (cdr ty2s)
                         (unifier (car ty1s)
                                  (car ty2s)
                                  subst exp)))
               (report-unification-failure ty1 ty2 exp))))
        (else (report-unification-failure ty1 ty2 exp))))))
(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-types result-type)
                 (and (and (map (lambda (x) (no-occurrence? tvar x)) arg-types))
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
      (proc-type (arg-types result-type)
                 (append (map type-to-external-form arg-types)
                         (list '->
                               (type-to-external-form result-type))))
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
      (let-exp (vars exps body)
               (let loop ([lvars vars]
                          [exps exps]
                          [types '()]
                          [subst subst])
                 (if (null? lvars)
                     (type-of body
                              (extend-tenv* vars types tenv)
                              subst)
                     (cases answer (type-of (car exps) tenv subst)
                       (an-answer (exp1-type subst)
                                  (loop (cdr lvars)
                                        (cdr exps)
                                        (append types (list exp1-type))
                                        subst))))))
      (proc-exp (vars otypes body)
                (let ((var-types (map otype->type otypes)))
                  (cases answer (type-of body
                                         (extend-tenv* vars var-types tenv)
                                         subst)
                    (an-answer (body-type subst)
                               (an-answer (proc-type var-types body-type)
                                          subst)))))
      (call-exp (rator rands)
                (let ((result-type (fresh-tvar-type)))
                  (let loop ([rands rands]
                             [types '()]
                             [subst subst])
                    (if (null? rands)
                        (cases answer (type-of rator tenv subst)
                          (an-answer (rator-type subst)
                                     (let ((subst
                                            (unifier rator-type
                                                     (proc-type types result-type)
                                                     subst exp)))
                                       (an-answer result-type subst))))
                        (cases answer (type-of (car rands) tenv subst)
                          (an-answer (exp1-type subst)
                                     (loop (cdr rands)
                                           (append types (list exp1-type))
                                           subst)))))))
      (letrec-exp (p-result-otypes p-names b-varss b-var-otypess p-bodies letrec-body)
                  (let ((p-result-types (map otype->type p-result-otypes))
                        (b-var-typess (map (lambda (var-otypes)
                                             (map otype->type var-otypes))
                                           b-var-otypess)))
                    (let ((tenv-for-letrec-body (extend-tenv-rec p-names
                                                                 b-var-typess
                                                                 p-result-types
                                                                 tenv)))
                      (let loop ([b-varss b-varss]
                                 [b-var-typess b-var-typess]
                                 [p-bodies p-bodies]
                                 [p-result-types p-result-types]
                                 [subst subst])
                        (if (null? b-varss)
                            (type-of letrec-body tenv-for-letrec-body subst)
                            (cases answer (type-of (car p-bodies)
                                                   (extend-tenv* (car b-varss)
                                                                 (car b-var-typess)
                                                                 tenv-for-letrec-body)
                                                   subst)
                              (an-answer (exp1-type subst)
                                         (let ((subst
                                                (unifier (car p-result-types) exp1-type subst exp)))
                                           (loop (cdr b-varss)
                                                 (cdr b-var-typess)
                                                 (cdr p-bodies)
                                                 (cdr p-result-types)
                                                 subst)))))))))
      )))


(run "proc(x:? y:? z:?) if y then x else z")
(run "letrec ? add(x:? y:? z:?) = if zero?(x) then y else z
                ? dec(x:? y:? z:?) = if zero?(z) then x else y in if zero?(0) then dec else add")