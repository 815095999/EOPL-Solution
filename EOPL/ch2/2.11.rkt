#lang racket
(define empty-env (lambda () '()))
(define empty-env?
  (lambda (env)
    (eqv? env (empty-env))))
(define extend-env
  (lambda (var val env)
    (cons (cons (list var) (list val)) env)))
(define extend-env*
  (lambda (lvar lval env)
    (cons (cons lvar lval)
          env)))
(define find-var-in-ribs
  (lambda (var lvar lval)
    (cond ((null? lvar) #f)
          ((equal? var (car lvar)) (list (car lval)))
          (else (find-var-in-ribs var (cdr lvar) (cdr lval))))))
(define apply-env
  (lambda (env search-var)
    (if (null? env)
        (report-no-binding-found search-var)
        (let ((saved-lvar (caar env))
              (saved-lval (cdar env))
              (saved-env (cdr env)))
          (let ((ans (find-var-in-ribs search-var saved-lvar saved-lval)))
            (if ans (car ans) (apply-env saved-env search-var)))))))
(define report-no-binding-found
  (lambda (search-var)
    (error 'apply-env "No binding for ~s" search-var)))

