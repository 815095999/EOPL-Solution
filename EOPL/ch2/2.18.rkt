#lang racket
(define number->sequence
  (lambda (num)
    (list num '() '())))
(define current-element
  (lambda (lst)
    (car lst)))
(define move-to-left
  (lambda (lst)
    (if (at-left-end? lst)
        (error "at-left-end!")
        (list (caadr lst) (cdadr lst) (cons (current-element lst) (caddr lst))))))
(define move-to-right
  (lambda (lst)
    (if (at-right-end? lst)
        (error "at-right-end!")
        (list (caaddr lst) (cons (current-element lst) (cadr lst)) (cdaddr lst)))))
(define insert-to-left
  (lambda (num lst)
    (list (car lst) (cons num (cadr lst)) (caddr lst))))
(define insert-to-right
  (lambda (num lst)
    (list (car lst) (cadr lst) (cons num (caddr lst)))))
(define at-left-end?
  (lambda (lst)
    (null? (cadr lst))))
(define at-right-end?
  (lambda (lst)
    (null? (caddr lst))))