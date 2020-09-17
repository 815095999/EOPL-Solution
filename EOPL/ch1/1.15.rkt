#lang racket
; duple: int x schemevalue -> listof(schemevalue)
; usage: generate a list consists of x, in which the number of x is n.
(define duple
  (lambda (n x)
    (if (= n 0)
        '()
        (cons x (duple (- n 1) x)))))