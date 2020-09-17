#lang racket
(define empty-stack
  (lambda ()
    (lambda (cmd)
      (cond ((equal? cmd 'pop)
             (error 'empty-stack "pop on empty stack"))
            ((equal? cmd 'top)
             (error 'empty-stack "top on empty-stack"))
            ((equal? cmd 'empty?) #t)
            (else (error "unknown cmd"))))))
(define push
  (lambda (val st)
    (lambda (cmd)
      (cond ((equal? cmd 'pop) st)
            ((equal? cmd 'top) val)
            ((equal? cmd 'empty?) #f)
            (else (error "unknown cmd"))))))
(define pop
  (lambda (st)
    (st 'pop)))
(define top
  (lambda (st)
    (st 'top)))
(define empty-stack?
  (lambda (st)
    (st 'empty?)))