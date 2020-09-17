#lang eopl
(define value?
  (lambda (s)
    #t))
(define-datatype env env?
  (empty-env)
  (extend-env
   (saved-var symbol?)
   (saved-val value?)
   (saved-env env?)))
(define apply-env
  (lambda (environment search-var)
    (cases env environment
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                     (if (equal? saved-var search-var)
                         saved-val
                         (apply-env search-var saved-env))))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))
(define has-binding?
  (lambda (environment search-var)
    (cases env environment
      (empty-env () #f)
      (extend-env (var val _env)
                  (if (equal? var search-var)
                      #t
                      (has-binding? _env search-var))))))