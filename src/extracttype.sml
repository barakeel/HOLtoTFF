structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype

fun alltypel2 varl = 
  case varl of
    [] => []
  | a :: m => type_of a :: alltypel2 m

fun alltypel propl = erasedouble (alltypel2 (all_varsl propl))

fun alphatypel propl = type_varsl (alltypel propl)
 

(* can be applied after erasing tffconstant 
because there is no need of a type for them *)

fun simpletypel fvc_arity_nm_typenm =
  case fvc_arity_nm_typenm of
    [] => []
  | (fvc,0,nm,typenm) :: m => typenm :: simpletypel m  
  | a :: m => simpletypel m 

end
