#lang racket
(define subst
  (lambda (new old slist)
    (if (null? slist)
        ’()
        (cons (subst-in-s-exp new old (car slist))
              (subst new old (cdr slist))))))
