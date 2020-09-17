"module tables
   interface [opaque table
              empty : table
              add-to-table : (int -> (int -> (table -> table)))
              lookup-in-table : (int -> (table -> int))]
   body
     [type table = (int -> int)
      empty = lambda (x : int) 0
      add-to-table = proc (x : int) proc (y : int) proc (tab : table)
                        proc (z : int) if zero?(-(x,z)) then y else (tab z)
      lookup-in-table = proc (x : int) proc (tab : table) (tab x)]
   let empty = from tables take empty
   in let add-binding = from tables take add-to-table
      in let lookup = from tables take lookup-in-table
         in let table1 = (((add-binding 3) 300) (((add-binding 4) 400) (((add-binding 3) 600) empty)))
            in -(((lookup 4) table1), ((lookup 3) table1))"