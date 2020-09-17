#lang eopl

; part1
module from-int-maker
  interface
   ((ints : [opaque t
             zero : t
             succ : (t -> t)
             pred : (t -> t)
             is-zero : (t -> bool)])
    => [from-int : (int -> from ints take t)])
  body
  module-proc (ints : [opaque t
                       zero : t
                       succ : (t -> t)
                       pred : (t -> t)
                       is-zero : (t -> bool)])
   [from-int =  let t = from ints take t
                in letrec t from-int(x : int) = 
                            if zero?(x)
                            then from ints take zero
                            else (from int take succ
                                   (from-int -(x,1)))
                   in from-int]

; part2
module to-int-maker
  interface
   ((ints : [opaque t
             zero : t
             succ : (t -> t)
             pred : (t -> t)
             is-zero : (t -> bool)])
    => [to-int : (from ints take t -> int)])
body
  module-proc (ints : [opaque t
                       zero : t
                       succ : (t -> t)
                       pred : (t -> t)
                       is-zero : (t -> bool)])
  [to-int = let z? = from ints take is-zero
            in let p = from ints take pred
            in letrec int to-int(x : from ints take t)
                          = if (z? x)
                            then 0
                            else -((to-int (p x)), -1)
               in to-int]

module ints1
  interface [opaque t
             zero : t
             succ : (t -> t)
             pred : (t -> t)
             is-zero : (t -> bool)]
  body [type t = int
        zero = 0
        succ = proc(x : t) -(x,-5)
        pred = proc(x : t) -(x,5)
        is-zero = proc (x : t) zero?(x)]

module ints2
  interface [opaque t
             zero : t
             succ : (t -> t)
             pred : (t -> t)
             is-zero : (t -> bool)]
  body [type t = int
        zero = 0
        succ = proc(x : t) -(x,3)
        pred = proc(x : t) -(x,-3)
        is-zero = proc (x : t) zero?(x)]

module ints1-to-int
  interface [to-int : (from ints1 take t -> int)]
  body (to-int-maker ints1)

module ints2-to-int
  interface [to-int : (from ints2 take t -> int)]
  body (to-int-maker ints2)

module ints1-from-int
  interface [from-int : (int -> from ints1 take t)]
  body (from-int-maker ints1)

module ints2-from-int
  interface [from-int : (int -> from ints2 take t)]
  body (from-int-maker ints2)

let f1 = from ints1-from-int take from-int
  in let f2 = from ints2-from-int take from-int
  in let t1 = from ints1-to-int take to-int
  in let t2 = from ints2-to-int take to-int
  in -((t1 (f1 5)),(t2 (f2 6)))