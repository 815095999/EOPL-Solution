#lang racket
; flatten: slist -> listof(sym)
; usage: returns a list of the symbols contained in slist in the order in which
;        they occur when slist is printed.
(define flatten
  (lambda (slist)
    (if (null? slist)
        '()
        (let ((fir (car slist)))
          (append (if (list? fir) (flatten fir) (list fir))
                  (flatten (cdr slist)))))))