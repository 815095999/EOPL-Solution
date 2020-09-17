#lang eopl
; 1.(lambda (x y) (p (+ 8 x) (q y)))
(lambda (x y cont)
  (q y (lambda (v1)
         (p (+ 8 x) v1 cont))))

; 2.(lambda (x y u v) (+ 1 (f (g x y) (+ u v))))
(lambda (x y u v cont)
  (g x y (lambda (v1)
           (f v1 (+ u v) (lambda (v2)
                           (cont (+ 1 v2)))))))

; 3.(+ 1 (f (g x y) (+ u (h v))))
(h v (lambda (v1)
       (g x y (lambda (v2)
                (f v2 (+ u v1) (lambda (v3)
                                 (cont (+ 1 v3))))))))

; 4.(zero? (if a (p x) (p y)))
(p x (lambda (v1)
       (p y (lambda (v2)
              ((lambda (v3) (cont (zero? v3)))
               (if a v1 v2))))))
; 5.(zero? (if (f a) (p x) (p y)))
(p x (lambda (v1)
       (p y (lambda (v2)
              (f a (lambda (v3)
                 ((lambda (v4) (cont (zero? v4)))
                  (if v3 v1 v2))))))))
; 6.(let ((x (let ((y 8)) (p y)))) x)
(let ((y 8))
  (p y (lambda (v1)
         (let ((x v1))
           (cont x)))))
; 7.(let ((x (if a (p x) (p y)))) x)
(p x (lambda (v1)
       (p y (lambda (v2)
              (let ((x (if a v1 v2)))
                (cont x))))))