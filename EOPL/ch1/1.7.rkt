#lang racket
(define list-rec
  (lambda (lst n)
    (if (null? lst)
        #f
        (if (= n 0)
            (car lst)
            (list-rec (cdr lst) (- n 1))))))
(define nth-element
  (lambda (lst n)
    (let ((ans (list-rec lst n)))
      (if ans ans (report-error lst n)))))
(define report-error
  (lambda (lst n)
    (error 'nth-element "~s does not have ~s elements.~%" lst n)))