#lang racket
; swapper: sym x sym x slist -> slist
; usage: returns a list the same as slist, but with all occurrences of s1
;        replaced by s2 and all occurrences of s2 replaced by s1
(define swapper
  (lambda (s1 s2 slist)
    (if (null? slist)
        '()
        (let ((fir (car slist))
              (rest-lst (cdr slist)))
          (cons (if (symbol? fir)
                    (cond ((equal? fir s1) s2)
                          ((equal? fir s2) s1)
                          (else fir))
                    (swapper s1 s2 fir))
                (swapper s1 s2 rest-lst))))))