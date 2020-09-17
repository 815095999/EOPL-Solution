#lang eopl
(define-datatype bintree bintree?
  (leaf-node (num integer?))
  (interior-node (key symbol?)
                 (left bintree?)
                 (right bintree?)))
(define bintree-to-list
  (lambda (bin)
    (cases bintree bin
      (leaf-node (val)
                 (list 'leaf-node val))
      (interior-node (key left right)
                     (list 'interior-node key (bintree-to-list left) (bintree-to-list right))))))
(define max-interior
  (lambda (bin)
    (caar (dfs bin))))
(define dfs
  (lambda (bin)
    (cases bintree bin
      (leaf-node (val)
                 (cons (cons #f val) val))
      (interior-node (key left right)
                     (letrec ((lans (dfs left))
                              (rans (dfs right))
                              (sum (+ (cdr lans) (cdr rans))))
                       (cons (merge (car lans) (merge (car rans) (cons key sum)))
                             sum))))))
(define merge
  (lambda (x y)
    (cond ((not (car x)) y)
          ((not (car y)) x)
          ((> (cdr x) (cdr y)) x)
          (else y))))
(define tree-1 (interior-node 'foo (leaf-node 2) (leaf-node 3)))
(define tree-2 (interior-node 'bar (leaf-node -1) tree-1))
(define tree-3 (interior-node 'baz tree-2 (leaf-node 1)))
(display (max-interior tree-1))
(display (max-interior tree-2))
(display (max-interior tree-3))
