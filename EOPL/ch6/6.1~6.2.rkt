; 6.1
; 递归过程中不会改变pc, apply-cont过程中也不会改变pc


; 6.2
(fib/k n+1 g)
=(fib/k n (lambda (v1) (fib/k n-1 (lambda (v2) (g (+ v1 v2))))))
=((lambda (v1) (fib/k n-1 (lambda (v2) (g (+ v1 v2))))) (fib n))
=(fib/k n-1 (lambda (v2) (g (+ (fib n) v2))))
=((lambda v2 (g (+ (fib n) v2))) (fib n-1))
=(g (+ (fib n) (fib n-1)))
=(g (fib (n+1)))

