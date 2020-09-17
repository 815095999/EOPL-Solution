#lang racket
; every?: pred x list -> bool
; usage: returns #f if any element of lst fails to satisfy pred, and returns #t otherwise.

(define every?
  (lambda (pred lst)
    (if (null? lst)
        #t
        (and (pred (car lst))
             (every? pred (cdr lst))))))