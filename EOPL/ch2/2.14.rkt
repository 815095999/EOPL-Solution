#lang racket
(define empty-env
  (lambda ()
    (list (lambda (search-var)
            (report-no-binding-found search-var))
          (lambda () #t)
          (lambda (search-var) #f))))
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (list (lambda (search-var)
            (if (equal? search-var saved-var)
                saved-val
                (apply-env saved-env search-var)))
          (lambda () #f)
          (lambda (search-var)
            (if (equal? search-var saved-var)
                #t
                (has-binding? saved-env search-var))))))
(define apply-env
  (lambda (env search-var)
    ((car env) search-var)))
(define report-no-binding-found
  (lambda (search-var)
    (error 'apply-env "No binding for ~s" search-var)))
(define empty-env?
  (lambda (env)
    ((cadr env))))
(define has-binding?
  (lambda (env search-var)
    ((caddr env) search-var)))
