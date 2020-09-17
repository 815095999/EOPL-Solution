#lang racket
(define N 10)
(define zero
  (lambda ()
    '()))
(define is-zero?
  (lambda (n)
    (null? n)))
(define successor
  (lambda (n)
    (cond ((is-zero? n) '(1))
          ((= (- N 1) (car n))
           (cons 0 (successor (cdr n))))
          (else (cons (+ (car n) 1) (cdr n))))))
(define predecessor
  (lambda (n)
    (cond ((equal? n '(1)) (zero))
          ((= (car n) 0)
           (cons (- N 1) (predecessor (cdr n))))
          (else (cons (- (car n) 1) (cdr n))))))
(define factorial
  (lambda (n)
    (if (is-zero? n)
        (successor (zero))
        (multiple n (factorial (predecessor n))))))
(define plus
  (lambda (x y)
    (if (is-zero? x)
        y
        (successor (plus (predecessor x) y)))))
(define multiple
  (lambda (x y)
    (if (is-zero? x)
        (zero)
        (plus y (multiple (predecessor x) y)))))

(display (factorial '(10)))