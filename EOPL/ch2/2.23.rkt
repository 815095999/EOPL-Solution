#lang eopl
(define identifier?
  (lambda (s)
    (and (symbol? s)
         (not (equal? s 'lambda)))))