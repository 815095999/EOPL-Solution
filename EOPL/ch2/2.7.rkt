#lang racket
(define empty-env (lambda () (list 'empty-env)))
(define extend-env
  (lambda (var val env)
    (list 'extend-env var val env)))
(define apply-env
  (lambda (ori-env search-var)
    (letrec ((loop (lambda (env)
                  (cond ((equal? (car env) 'empty-env) (report-no-binding-found search-var ori-env))
                        ((equal? (car env) 'extend-env)
                         (let ((saved-var (cadr env))
                               (saved-val (caddr env))
                               (saved-env (cadddr env)))
                           (if (equal? search-var saved-var)
                               saved-val
                               (loop saved-env))))
                        (else (report-invalid-env ori-env))))))
     (loop ori-env))))
(define report-no-binding-found
  (lambda (search-var env)
    (error 'apply-env "No binding for ~s in ~s" search-var env)))

(define report-invalid-env
  (lambda (env)
    (error 'apply-env "Bad environment: ~s" env)))