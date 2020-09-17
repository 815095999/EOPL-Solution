#lang eopl
module sum-prod-maker
  interface
    ((ints : [opaque t
              zero : t
              succ : (t -> t)
              pred : (t -> t)
              is-zero : (t -> bool)])
     => [plus : (from ints take t -> (from ints take t -> from ints take t))
         times : (from ints take t -> (from ints take t -> from ints take t))])
  body
   [plus = let t = from ints take t
           in let z? = from ints take is-zero
           in let s = from ints take succ
           in let p = from ints take pred
           in letrec t plus(x:int) = proc(y :int) if z?(y)
                                                  then x
                                                  else ((plus (s x)) (p y))
              in plus
    times =  let t = from ints take t
             in let z? = from ints take is-zero
             in let p = from ints take pred
             in letrec t times(x:int) =
                  letrec timesx(y:int) = if z?(y)
                                            then zero
                                            else ((plus x) (timesx (p y)))
                  in timesx
                in times]