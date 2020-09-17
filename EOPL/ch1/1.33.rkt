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
(define mark-leaves-with-red-depth
  (lambda (node)
    (dfs node 0)))
(define dfs
  (lambda (node deep)
    (let ((cont (contents-of node)))
      (if (leaf? node)
          deep
          (let ((delta (if (equal? cont 'red) 1 0)))
            (interior-node cont
                           (dfs (lson node) (+ deep delta))
                           (dfs (rson node) (+ deep delta))))))))