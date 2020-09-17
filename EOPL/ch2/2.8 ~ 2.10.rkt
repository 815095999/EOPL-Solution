#lang racket
(define empty-env (lambda () '()))
(define empty-env?
  (lambda (env)
    (eqv? env (empty-env))))
(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))
(define extend-env*
  (lambda (lvar lval env)
    (append (make-2-list lvar lval)
            env)))
(define make-2-list
  (lambda (x y)
    (cond ((null? x) '())
          (else (cons (cons (car x) (car y))
                      (make-2-list (cdr x) (cdr y)))))))
(define has-binding?
  (lambda (var env)
    (cond ((empty-env? env) #f)
          ((equal? (caar env) var) #t)
          (else (has-binding? var (cdr env))))))
(define find-value
  (lambda (env search-var)
    (let ((saved-var (caar env))
          (saved-val (cdar env))
          (saved-env (cdr env)))
      (if (equal? saved-var search-var)
          saved-val
          (apply-env saved-env search-var)))))
(define apply-env
 (lambda (env search-var)
   (if (has-binding? search-var env)
       (find-value env search-var)
       (report-no-binding-found search-var env))))
(define report-no-binding-found
  (lambda (search-var env)
    (error 'apply-env "No binding for ~s in ~s" search-var env)))

