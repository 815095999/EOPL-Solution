; 1. (int -> int)
; 2. ((t -> int) -> (t -> int))
; 3. (t -> t)
; 4. ((t1 -> t2) -> (t1 -> t2))
; 5. ((int -> t) -> t)
; 6. ((t1 -> t2) -> t2)
; 7. (bool -> int)
; 8. (bool -> (int -> int))
; 9. int
; 10. int
; 11. ((t -> int) -> ((int -> int) -> ((int -> bool) -> (t -> int))))
; 12. (int -> ((int -> bool) -> (((int->bool) -> int) -> int)))
; 13. no type, assume f: t1->t2, from proc(n) ( (f (d d)) n) we know f: t1 -> (t1 -> t2) , then t2 = (t1 -> t2) which is impossible

