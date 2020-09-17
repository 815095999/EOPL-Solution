#lang racket
; list-set: list x int x val -> list
; usage: returns a list like lst, except that the n-th element,
;        using zero-based indexing, is x.
(define list-set
  (lambda (lst n x)
    (if (= n 0)
        (cons x (cdr lst))
        (cons (car lst) (list-set (cdr lst) (- n 1) x)))))