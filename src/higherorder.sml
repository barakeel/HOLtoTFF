structure higherorder :> higherorder =
struct

open HolKernel listtools extract_var extracttype mydatatype

fun HIGHERORDER_ERR function message =
  HOL_ERR{origin_structure = "higherorder",
          origin_function = function,
          message = message}

(* VARIABLE *)
fun firstorderbvl bv_arity =
  case bv_arity of
    [] => true
  | (bv,arity) :: m => if arity = 0
                        then firstorderbvl m
                         else raise HIGHERORDER_ERR 
                                      "firstorderbvl" 
                                      ((term_to_string bv) ^ ": higher order" )

fun firstorderfvcdcl2 fvcdc_arity defined =
  case fvcdc_arity of
    [] => true
  | (fvcdc,arity) :: m => if is_member fvcdc (map fst defined)
                         then 
                           let val n = lookup fvcdc defined in
                             if arity = n 
                             then firstorderfvcdcl2 m defined
                             else raise HIGHERORDER_ERR 
                                          "firstorderfvcdc" 
                                          ((term_to_string fvcdc) ^ ": higher order" )
                           end
                         else firstorderfvcdcl2 m ((fvcdc,arity) :: defined)
 
fun firstorderfvcdcl fvcdc_arity = firstorderfvcdcl2 fvcdc_arity []

(* TYPE *)
(* test if some functions variables have boolean type as type argument *) (* so boolean are always on top *)
fun hasbooleanl var tyal =
  case tyal of
    [] => false 
  | (ty,arity) :: m => (
                      case (typecat ty) of
                      Booltype => raise HIGHERORDER_ERR 
                                   "hasbooleanl"
                                   ((term_to_string var) ^ ": has a boolean argument")
                      | _ => hasbooleanl var m
                      )

(* do a bit like nametype *)
fun booleaarityl var_arity = 
  case var_arity of
    [] => false
  | (var,arity) :: m => let val (argl,image) = dest_type_nb (type_of var,arity) in 
                         hasbooleanl var argl 
                         orelse 
                         booleaarityl m
                       end


end
