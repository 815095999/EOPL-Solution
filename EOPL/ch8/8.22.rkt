#lang eopl
module equality-maker
  interface
   ((ints : [opaque t
             zero: t
             succ: (t -> t)
             pred: (t -> t)
             is-zero : (t -> bool)])
     => [equal : (from ints take t -> (from ints take t -> bool))])
  body
  module-proc (ints : [opaque t
                       zero : t
                       succ : (t -> t)
                       pred : (t -> t)
                       is-zero : (t -> bool)])
    [transparent t = from ints take t
     equal = letrec bool equal(x:t) = proc (y : t)
                                      if is-zero(x)
                                      then if is-zero(y)
                                           then true
                                           else false
                                      else ((equal (from ints take pred x))
                                            (from ints take pred y))
             in equal]