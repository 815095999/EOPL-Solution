#lang eopl
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define-datatype lc-exp lc-exp?
  (var-exp (var identifier?))
  (lambda-exp (bound-vars (list-of identifier?)) (body lc-exp?))
  (app-exp (rator lc-exp?) (rands (list-of lc-exp?))))
(define parse
  (lambda (lst)
    (cond ((identifier? lst) (var-exp lst))
          ((equal? (car lst) 'lambda)
           (lambda-exp (cadr lst) (parse (caddr lst))))
          (else (app-exp (parse (car lst)) (map parse (cdr lst)))))))
