#lang racket
; count-occurrences: sym x slist -> int
; usage: returns the number of occurrences of s in slist.
(define count-occurrences
  (lambda (sym slist)
    (if (null? slist)
        0
        (let ((fir (car slist))
              (rest (cdr slist)))
          (+ (if (symbol? fir)
                 (if (equal? fir sym) 1 0)
                 (count-occurrences sym fir))
             (count-occurrences sym rest))))))