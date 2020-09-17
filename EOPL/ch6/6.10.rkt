#lang eopl
(define list-sum
  (lambda (loi)
    (list-sum/k loi 0)))
(define list-sum/k
  (lambda (loi cont)
    (if (null? loi)
        cont
        (list-sum/k (cdr loi)
                    (+ cont (car loi))))))