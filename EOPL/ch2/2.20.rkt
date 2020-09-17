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

; car表示当前子树，cdr表示父亲到当前子树的路径
; 路径由若干3-list组成，一个3-list包含的元素分别为当前节点是父亲的左或右子树、父亲节点值、另一子树
(define loc cons)
(define subtree car)
(define route cdr)
(define number->loc
  (lambda (num)
    (cons (number->bintree num)
          '())))
(define current-element-loc
  (lambda (loc)
    (current-element (subtree loc))))
(define move-to-left-loc
  (lambda (loc)
    (cons (move-to-left (subtree loc))
          (cons (list 'l (current-element-loc loc) (move-to-right (subtree loc)))
                (route loc)))))
(define move-to-right-loc
  (lambda (loc)
    (cons (move-to-right (subtree loc))
          (cons (list 'r (current-element-loc loc) (move-to-left (subtree loc)))
                (route loc)))))
(define insert-to-left-loc
  (lambda (num loc)
    (cons (insert-to-left num (subtree loc))
          (route loc))))
(define insert-to-right-loc
  (lambda (num loc)
    (cons (insert-to-right num (subtree loc))
          (route loc))))
(define at-leaf-loc?
  (lambda (loc)
    (at-leaf? (subtree loc))))
(define caddadr
  (lambda (lst)
    (caddr (cadr lst))))
(define move-up-loc
  (lambda (loc)
    (cons (if (equal? (caar (route loc)) 'l)
              (fork (cadar (route loc))
                    (subtree loc)
                    (caddar (route loc)))
              (fork (cadar (route loc))
                    (caddar (route loc))
                    (subtree loc)))
          (cdr (route loc)))))
(define at-root?
  (lambda (loc)
    (null? (cdr loc))))

(define a (number->loc 3))
(define b (insert-to-left-loc 4 a))
(define c (insert-to-right-loc 5 b))
(define d (insert-to-left-loc 7 c))
(define e (move-to-left-loc (move-to-left-loc d)))
