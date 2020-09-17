#lang racket
; list-index: pred x list -> int
; usage: returns the 0-based position of the first element of lst that satisfies
;        the predicate pred. If no element of lst satisfies the predicate, then
;        list-index returns #f.
(define list-index
  (lambda (pred lst)
    (if (null? lst)
        #f
        (if (pred (car lst))
            0
            (let ((ans (list-index pred (cdr lst))))
              (if ans (+ ans 1) #f))))))