#lang racket
; var-exp: var->lc-exp
(define var-exp
  (lambda (var)
    var))
; lambda-exp: var x lc-exp -> lc-exp
(define lambda-exp
  (lambda (var body)
    (list 'lambda var body)))
; app-exp: lc-exp x lc-exp -> lc-exp
(define app-exp
  (lambda (rator rand)
    (list rator rand)))
; var-exp?: lc-exp -> bool
(define var-exp?
  (lambda (lexp)
    (symbol? lexp)))
; lambda-exp? : lc-exp -> bool
(define lambda-exp?
  (lambda (lexp)
    (equal? (car lexp) 'lambda)))
; app-exp? : lc-exp x lc-exp -> bool
(define app-exp?
  (lambda (lexp)
    (= (length lexp) 2)))
; var-exp->var: lc-exp -> var
(define var-exp->var
  (lambda (lexp)
    lexp))
; lambda-exp->bound-var: lc-exp -> var
(define lambda-exp->bound-var
  (lambda (lexp)
    (cadr lexp)))
; lambda-exp->body: lc-exp -> lc-exp
(define lambda-exp->body
  (lambda (lexp)
    (caddr lexp)))
; app-exp->rator: lc-exp -> lc-exp
(define app-exp->rator
  (lambda (lexp)
    (car lexp)))
; app-exp->rand
(define app-exp->rand
  (lambda (lexp)
    (cadr lexp)))
(define occurs-free?
  (lambda (search-var exp)
    (cond ((var-exp? exp)
           (eqv? search-var (var-exp->var exp)))
          ((lambda-exp? exp)
           (and (not (eqv? search-var (lambda-exp->bound-var exp)))
                (occurs-free? search-var (lambda-exp->body exp))))
          (else (or (occurs-free? search-var (app-exp->rator exp))
                    (occurs-free? search-var (app-exp->rand exp)))))))