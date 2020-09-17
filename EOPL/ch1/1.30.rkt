#lang racket
; sort/predicate: pred x loi -> loi
; usage: returns a list of elements sorted by the predicate.
(define sort/predicate
  (lambda (pred loi)
    (if (null? loi)
        '()
        (let ((rest (sort/predicate pred (cdr loi))))
          (insert pred (car loi) rest)))))
; insert: pred x int x loi -> loi
; usage: insert x in loi, retaining the order indicated by pred.
(define insert
  (lambda (pred num loi)
    (if (null? loi)
        (list num)
        (if (pred num (car loi))
            (cons num loi)
            (cons (car loi)
                  (insert pred num (cdr loi)))))))