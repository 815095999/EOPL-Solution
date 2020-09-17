#lang eopl
; apparently this solution also works in O(n) time because of the newref operation, but we can solve this problem using the method of vector in C++, we pre-allocated some space and when there's no enough space we double it.
; ------------------------------------------------------------------------------
; Storage

; empty-store: () -> sto
(define empty-store
  (lambda () (make-vector 0)))

(define the-store 'uninitialized)

; get-store: () -> sto
(define get-store
  (lambda () the-store))

; initialize-store!: () -> unspecified
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; reference?: schemeval -> bool
(define reference?
  (lambda (x) (integer? x)))

(define copy
  (lambda (new old now)
    (if (= now (vector-length old))
        'ok
        (begin (vector-set! new now (vector-ref old now))
               (copy new old (+ now 1))))))
; newref: expval -> ref
(define newref
  (lambda (val)
    (let* ((store-length (vector-length the-store))
           (new-store (make-vector (+ store-length 1))))
      (copy new-store the-store 0)
      (set! the-store new-store)
      (vector-set! the-store store-length val)
      store-length)))

; deref: ref -> expval
(define deref
  (lambda (ref)
   (vector-ref the-store ref)))

; setref!: ref x expval -> unspecified
(define setref!
  (lambda (ref val)
    (vector-set! the-store ref val)))

(define report-invalid-reference
  (lambda (ref store1)
    (eopl:error "invalid reference! ~s ~s" ref store1)))