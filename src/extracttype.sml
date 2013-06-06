structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype extractvar


fun alltypel2 var_narg_nm = 
  case var_narg_nm of
    [] => []
  | (var,narg,nm) :: m => (type_of var) :: alltypel2 m

fun alltypel var_narg_nm = erasedouble (alltypel2 (var_narg_nm))
 
fun alphatypel var_narg_nm = type_varsl (alltypel var_narg_nm)


end
