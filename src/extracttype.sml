structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype

fun alltypel2 varl = 
  case varl of
    [] => []
  | a :: m => type_of a :: alltypel2 m

fun alltypel propl = erasedouble (alltypel2 (all_varsl propl))

fun alphatypel propl = type_varsl (alltypel propl)

fun simpletypel2 typel =
 case typel of
   [] => []  
 | a :: m => (
             case typecat a of
               Simpletype => a :: simpletypel2 m
             | _ => simpletypel2 m  
             )

fun simpletypel propl = simpletypel2 (alltypel propl)


end
