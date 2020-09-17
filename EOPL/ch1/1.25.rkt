#lang racket
; exist?: pred x list -> bool
; usage: returns #t if any element of lst satisfies pred, and returns #f otherwise.
(define exists?
  (lambda (pred lst)
    (if (null? lst)
        #f
        (or (pred (car lst))
            (exists? pred (cdr lst))))))