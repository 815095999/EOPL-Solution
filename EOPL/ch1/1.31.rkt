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