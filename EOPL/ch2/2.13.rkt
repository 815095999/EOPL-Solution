#lang racket
(define empty-env
  (lambda ()
    (cons (lambda (search-var)
            (report-no-binding-found search-var))
          (lambda () #t))))
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (cons (lambda (search-var)
            (if (equal? search-var saved-var)
                saved-val
                (apply-env saved-env search-var)))
          (lambda () #f))))
(define apply-env
  (lambda (env search-var)
    ((car env) search-var)))
(define report-no-binding-found
  (lambda (search-var)
    (error 'apply-env "No binding for ~s" search-var)))
(define empty-env?
  (lambda (env)
    ((cdr env))))
