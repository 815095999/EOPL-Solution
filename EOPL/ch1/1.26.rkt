#lang racket
; up: list -> list
; usage: removes a pair of parentheses from each top-level element of lst.
;        If a top-level element is not a list, it is included in the result, as is.
(define up
  (lambda (lst)
    (if (null? lst)
        '()
        (let ((fir (car lst)))
          (append (if (list? fir)
                      fir
                      (list fir))
                  (up (cdr lst)))))))