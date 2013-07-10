structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype extractvar

fun EXTRACTTYPE_ERR function message =
  HOL_ERR{origin_structure = "extracttype",
          origin_function = function,
          message = message}

(* on the result of extract_var *)
(* shouldn't be necessary *)

fun all_typelowestarity2 varal = 
  case varal of
    [] => []
  | (var,arity) :: m => (type_of var,arity) :: all_typelowestarity2 m

fun all_typelowestarity term = 
  let val varal = collapse_lowestarity (map fst (nullify_bval (extract_var term))) in
    erase_double (all_typelowestarity2 varal)
  end
  
(* on the result of all_typelowestarity *)
fun get_simpletyal tyal =
  case tyal of
    [] => []
  | (ty,0) :: m => (ty,0) :: get_simpletyal m
  | a :: m => get_simpletyal m

fun get_compoundtyal tyal =
  case tyal of
    [] => []
  | (ty,0) :: m => get_compoundtyal m
  | (ty,arity) :: m => (ty,arity) :: get_compoundtyal m


(* recursive dest_type with a bound *)
(* type are always considered with their arity *)
fun dest_type_nb (ty,arity) = 
  case arity of
    0 => ([],(ty,0))
  | n => if n < 0 
         then raise EXTRACTTYPE_ERR "dest_type_nb" "negative number"
         else
           let val (str,list) = dest_type ty in 
           let 
             val ty1 = hd list
             val ty2 = hd (tl list) 
           in
           let val resl = dest_type_nb (ty2,(n-1)) in
           let
             val argl = fst resl
             val image = snd resl 
           in
             ((ty1,0) :: argl,image) 
           end end end end
        
 

end
