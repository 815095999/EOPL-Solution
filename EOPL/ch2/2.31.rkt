#lang eopl
(define-datatype prefix-exp prefix-exp?
  (const-exp (num integer?))
  (diff-exp (operand1 prefix-exp?)
            (operand2 prefix-exp?)))

(define move
  (lambda (lst num)
    (if (= num 0)
        lst
        (move (cdr lst) (- num 1)))))
(define parse-with-length
  (lambda (lst)
    (cond ((number? (car lst))
           (cons (const-exp (car lst))
                 1))
          (else (letrec ((lans (parse-with-length (cdr lst)))
                         (rans (parse-with-length (move (cdr lst) (cdr lans)))))
                  (cons (diff-exp (car lans) (car rans))
                        (+ 1 (cdr lans) (cdr rans))))))))
(define parse
  (lambda (lst)
    (car (parse-with-length lst))))