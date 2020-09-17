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
(define combine
  (lambda (x y)
    (if y (cons x y) #f)))
;; 如果按照题意来写的话，查找的值在根节点就会出现问题
(define path
  (lambda (n bst)
    (cond ((null? bst) #f)
          ((leaf? bst) (if (equal? bst n) '() #f))
          ((equal? n (contents-of bst)) '())
          ((< n (contents-of bst))
           (combine 'left (path n (lson bst))))
          (else
           (combine 'right (path n (rson bst)))))))