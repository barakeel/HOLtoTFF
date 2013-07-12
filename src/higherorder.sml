structure higherorder :> higherorder =
struct

open HolKernel 
     listtools tools 

fun HIGHERORDER_ERR function message =
  HOL_ERR {origin_structure = "higherorder",
           origin_function = function,
           message = message}

(* VARIABLE *)
fun firstorder_bval bval =
  case bval of
    [] => true
  | (bv,arity) :: m => 
    if arity = 0
    then firstorder_bval m
    else raise HIGHERORDER_ERR "firstorder_bvl" 
                 ((term_to_string bv) ^ " used with higher order" )

fun firstorder_fvcal_aux fvcal fvclal =
  case fvcal of
    [] => true
  | (fvc,arity) :: m => 
    if arity = lookup fvc fvclal
    then firstorder_fvcal_aux m fvclal
    else raise HIGHERORDER_ERR "firstorderfvcdc"  
                 ((term_to_string fvc) ^ " used with higher order" )
                  
fun firstorder_fvcal fvcal = 
  firstorder_fvcal_aux fvcal (collapse_lowestarity fvcal)                        

end
