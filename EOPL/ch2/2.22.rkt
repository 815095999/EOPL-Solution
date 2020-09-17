#lang eopl
(define value? (lambda (x) #t))
(define-datatype stack stack?
  (empty-stack)
  (non-empty-stack
   (val value?)
   (rest-stack stack?)))
(define push
  (lambda (val st)
    (non-empty-stack val st)))
(define pop
  (lambda (st)
    (cases stack st
      (empty-stack () (eopl:error "pop on empty-stack"))
      (non-empty-stack (val rest-stack) rest-stack))))
(define top
  (lambda (st)
    (cases stack st
      (empty-stack () (eopl:error "top on empty-stack"))
      (non-empty-stack (val rest-stack) val))))
(define empty-stack?
  (lambda (st)
    (cases stack st
      (empty-stack () #t)
      (non-empty-stack (x1 x2) #f))))