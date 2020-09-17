#lang racket
(define leaf
  (lambda (num)
    num))
(define interior-node
  (lambda (sym lson rson)
    (list sym lson rson)))
(define leaf? number?)
(define lson cadr)
(define rson caddr)
(define contents-of
  (lambda (node)
    (if (leaf? node) node (car node))))
(define solve
  (lambda (node num)
    (if (leaf? node)
        (cons num (+ num 1))
        (let ((lans (solve (lson node) num)))
          (let ((rans (solve (rson node) (cdr lans))))
            (cons (interior-node (contents-of node)
                                 (car lans)
                                 (car rans))
                  (cdr rans)))))))
(define number-leaves
  (lambda (node)
    (car (solve node 0))))