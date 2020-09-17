#lang racket
(define number-elements
  (lambda (lst)
    (if (null? lst)
        '()
        (g (list 0 (car lst)) (number-elements (cdr lst))))))
(define g
  (lambda (lst1 lst2)
    (cons lst1
            (map (lambda (x)
                   (list (+ 1 (car x))
                         (cadr x)))
                 lst2))))