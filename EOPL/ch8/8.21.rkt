#lang eopl
module double-arith-maker
  interface
   ((ints : [opaque t
             zero: t
             succ: (t -> t)
             pred: (t -> t)
             is-zero : (t -> bool)])
     => [opaque t
         zero: t
         succ : (t -> t)
         pred : (t -> t)
         is-zero : (t -> bool)])
  body
  module-proc (ints : [opaque t
                       zero : t
                       succ : (t -> t)
                       pred : (t -> t)
                       is-zero : (t -> bool)])
    [opaque t
     t = from ints import t
     zero = from ints import zero
     succ = proc (x : t) (from ints import succ
                               (from ints import succ t))
     pred = proc (x : t) (from ints import pred
                               (from ints import pred t))
     is-zero = from ints import is-zero]