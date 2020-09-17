#lang racket
(define leaf
  (lambda ()
    '()))
(define fork
  (lambda (n l r)
    (list n l r)))
(define number->bintree
  (lambda (num)
    (fork num '() '())))
(define current-element
  (lambda (bin)
    (car bin)))
(define move-to-left
  (lambda (bin)
    (cadr bin)))
(define move-to-right
  (lambda (bin)
    (caddr bin)))
(define at-leaf? null?)
(define insert-to-left
  (lambda (num bin)
    (fork (current-element bin)
          (fork num
                (move-to-left bin)
                (leaf))
          (move-to-right bin))))
(define insert-to-right
  (lambda (num bin)
    (fork (current-element bin)
          (move-to-left bin)
          (fork num
                (leaf)
                (move-to-right bin)))))