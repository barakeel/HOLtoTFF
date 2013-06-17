structure higherorder :> higherorder =
struct

open HolKernel listtools extractvar extracttype mydatatype

fun HIGHERORDER_ERR function message =
  HOL_ERR{origin_structure = "higherorder",
          origin_function = function,
          message = message}

(* VARIABLE *)
fun firstorderbvl bv_narg =
  case bv_narg of
    [] => true
  | (bv,narg) :: m => if narg = 0
                        then firstorderbvl m
                         else raise HIGHERORDER_ERR 
                                      "firstorderbvl" 
                                      ((term_to_string bv) ^ ": higher order" )

fun firstorderfvcdcl2 fvcdc_narg defined =
  case fvcdc_narg of
    [] => true
  | (fvcdc,narg) :: m => if ismember fvcdc (fstcomponent defined)
                         then 
                           let val n = lookup fvcdc defined in
                             if narg = n 
                             then firstorderfvcdcl2 m defined
                             else raise HIGHERORDER_ERR 
                                          "firstorderfvcdc" 
                                          ((term_to_string fvcdc) ^ ": higher order" )
                           end
                         else firstorderfvcdcl2 m ((fvcdc,narg) :: defined)
 
fun firstorderfvcdcl fvcdc_narg = firstorderfvcdcl2 fvcdc_narg []

(* TYPE *)
(* test if some functions variables have boolean type as type argument *) (* so boolean are always on top *)
fun hasbooleanl var ty_narg =
  case ty_narg of
    [] => false 
  | (ty,narg) :: m => (
                      case (typecat ty) of
                      Booltype => raise HIGHERORDER_ERR 
                                   "hasbooleanl"
                                   ((term_to_string var) ^ ": has a boolean argument")
                      | _ => hasbooleanl var m
                      )

(* do a bit like nametype *)
fun booleanargl var_narg = 
  case var_narg of
    [] => false
  | (var,narg) :: m => let val (argl,image) = desttypenb (type_of var,narg) in 
                         hasbooleanl var argl 
                         orelse 
                         booleanargl m
                       end


end
