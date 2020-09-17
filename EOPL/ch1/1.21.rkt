#lang racket
; product: listof(sym) x listof(sym) -> listof(list(sym,sym))
; usage: returns a list of 2-lists that represents the Cartesian product of
;        sos1 and sos2.
(define product
  (lambda (sos1 sos2)
    (if (null? sos1)
        '()
        (append (product-by-one (car sos1) sos2)
                (product (cdr sos1) sos2)))))
; product-by-one: sym x listof(sym) -> listof(list(sym,sym))
; usahe: returns a list of 2-lists that represents the Cartesian product of
;        sym1 and sos2.
(define product-by-one
  (lambda (sym1 sos2)
    (if (null? sos2)
        '()
        (cons (list sym1 (car sos2))
              (product-by-one sym1 (cdr sos2))))))