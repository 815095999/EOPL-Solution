#lang racket
; 1. 如果n为正,则拆分为 1 - (-1) - (-1) ... ,而-1是有限步的。
;    如果n为负,则拆分为1 - 1 - 1 ...。

; 2. & 3. 利用1.所定义的唯一表示法来表示每个数，这样可以不依赖于scheme value的限制。因为有唯一表示的限制，很难做到常数时间内同时处理三种情况。如果只需要处理加法情况，那么可以先直接加，然后在其他过程中归一化。但本质上没有什么区别。（github其他实现均有递归过程）
(define one
  (lambda ()
    'one))
(define diff
  (lambda (x y)
    (list 'diff x y)))
(define zero
  (lambda ()
    (diff (one) (one))))
(define neg-one
  (lambda ()
    (diff (zero) (one))))

(define is-zero?
  (lambda (n)
    (equal? n (zero))))
(define is-one?
  (lambda (n)
    (equal? n (one))))
(define neg-part caddr)
(define pos-part cadr)

(define >1?
  (lambda (n)
    (cond ((is-one? n) #f)
          ((is-one? (neg-part n)) #f)
          (else #t))))
(define successor
  (lambda (n)
    (cond ((is-one? n) (diff n (neg-one)))
          ((>1? n) (diff n (neg-one)))
          (else (pos-part n)))))
(define predecessor
  (lambda (n)
    (cond ((is-one? n) (zero))
          ((>1? n) (pos-part n))
          (else (diff n (one))))))
(define diff-tree-plus
  (lambda (x y)
    (cond ((is-zero? x) y)
          ((is-one? x) (successor y))
          ((>1? x) (diff-tree-plus (predecessor x) (successor y)))
          (else (diff-tree-plus (successor x) (predecessor y))))))