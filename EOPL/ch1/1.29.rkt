#lang racket
(define merge
  (lambda (loi1 loi2)
    (cond ((null? loi1) loi2)
          ((null? loi2) loi1)
          ((< (car loi1) (car loi2))
           (cons (car loi1)
                 (merge (cdr loi1) loi2)))
          (else
           (cons (car loi2)
                 (merge loi1 (cdr loi2)))))))

; sort: loi -> loi
; usage: returns a list of the elements of loi in ascending order
(define sort
  (lambda (lst)
    (if (null? lst)
        '()
        (merge (list (car lst))
               (sort (cdr lst))))))

