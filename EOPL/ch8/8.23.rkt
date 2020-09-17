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
                                      if from ints take is-zero(x)
                                      then if from ints take is-zero(y)
                                           then true
                                           else false
                                      else ((equal (from ints take pred x))
                                            (from ints take pred y))
             in equal]

module table-of
  interface
   ((ints : [opaque t
             zero: t
             succ: (t -> t)
             pred: (t -> t)
             is-zero : (t -> bool)])
     =>  [opaque table
              empty : table
              add-to-table : (int -> (from ints take t -> (table -> table)))
              lookup-in-table : (int -> (table -> from ints take t))])
  body
  module-proc (ints : [opaque t
             zero: t
             succ: (t -> t)
             pred: (t -> t)
             is-zero : (t -> bool)])
    [opaque table = (int -> from ints take t)
     empty = proc (x : int) from ints take zero
     add-to-table = proc (x : int) proc (y : from ints take t)
                       proc (tab : table) proc (z : int)
                          if equal(x,z) then z else (tab x) ; equal needs equality-maker
     lookup-in-table = proc (x) proc (tab) (tab x)]