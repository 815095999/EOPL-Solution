#lang racket
; remove : sym x listof(sym) -> listof(sym)
; usage : remove all the elements before the first occurrence of sym
;         (include first sym)
(define remove
  (lambda (s los)
    (if (null? los)
        '()
        (if (eqv? (car los) s)
            (cdr los)
            (remove s (cdr los))))))