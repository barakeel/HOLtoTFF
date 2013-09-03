structure basictools :> basictools =
struct

open HolKernel boolLib numSyntax

fun BASICTOOLS_ERR function message =
    HOL_ERR {origin_structure = "tffsyntax",
	           origin_function = function,
             message = message}


(* FUNCTION *)
fun repeat_n_fun n f x = 
  case n of
    0 => x
  | _ => if n < 0 
         then raise BASICTOOLS_ERR "repeat_n_fun" "negative number"  
         else f (repeat_n_fun (n - 1) f x)
    
fun inv f a b = f b a

(* ERROR HANDLING *)
fun success f x =
  (f x; true) handle _ => false
  
fun wrap s f m function x =
  function x               
  handle  
    HOL_ERR {origin_structure = s1, origin_function = f1, message = m1}
      => raise HOL_ERR {origin_structure = s ^ " - " ^ s1,
                        origin_function = f ^ " - " ^ f1,
                        message = m ^ " - " ^ m1}           
  | UNCHANGED => raise UNCHANGED
  | _ => raise HOL_ERR {origin_structure = s,
                        origin_function = f,
                        message = m}

end