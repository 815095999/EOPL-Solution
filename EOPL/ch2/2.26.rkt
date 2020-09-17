#lang eopl
(define-datatype red-blue-tree red-blue-tree?
  (red-node (x1 red-blue-tree?)
            (x2 red-blue-tree?))
  (blue-node (lst (list-of red-blue-tree?)))
  (leaf-node (x number?)))
(define rebuild
  (lambda (tree)
    (dfs tree 0)))
(define dfs
  (lambda (tree number)
    (cases red-blue-tree tree
      (red-node (x1 x2)
                (red-node (dfs x1 (+ number 1))
                          (dfs x2 (+ number 1))))
      (blue-node (lst)
                 (blue-node (map (lambda (tree) (dfs tree (+ number 1))) lst)))
      (leaf-node (x) (leaf-node number)))))