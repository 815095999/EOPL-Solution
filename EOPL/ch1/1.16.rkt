#lang racket
; invert: listof(2-list) -> listof(2-list)
; usage: invert every 2-list in the given list
(define invert
  (lambda (lst)
    (if (null? lst)
        '()
        (cons (invert-2-list (car lst))
              (invert (cdr lst))))))
; invert-2-list: 2-list -> 2-list
; usage: invert a 2-list
(define invert-2-list
  (lambda (lst)
    (list (cadr lst) (car lst))))