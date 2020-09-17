#lang eopl
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define-datatype lc-exp lc-exp?
  (var-exp (var identifier?))
  (lambda-exp (bound-var identifier?) (body lc-exp?))
  (app-exp (rator lc-exp?) (rand lc-exp?)))
(define unparse-lc-exp
  (lambda (exp)
    (cases lc-exp exp
      (var-exp (var) (symbol->string var))
      (lambda-exp (bound-var body)
                  (string-append "(lambda ("
                                  (symbol->string bound-var)
                                  ") "
                                  (unparse-lc-exp body)
                                  ")"))
      (app-exp (rator rand)
               (string-append "("
                              (unparse-lc-exp rator)
                              " "
                              (unparse-lc-exp rand)
                              ")")))))

(define lexp
  (lambda-exp 'x
       (lambda-exp 'y
            (lambda-exp 'x
                (app-exp
                      (lambda-exp 'x
				   (app-exp (var-exp 'x)
					    (var-exp 'y)))
		      (var-exp 'x))))))

(equal? (unparse-lc-exp lexp) "(lambda (x) (lambda (y) (lambda (x) ((lambda (x) (x y)) x))))")