structure extracttype :> extracttype =
struct

open HolKernel listtools mydatatype extractvar

fun EXTRACTTYPE_ERR function message =
  HOL_ERR{origin_structure = "extracttype",
          origin_function = function,
          message = message}

(* on the result of extract_var *)
fun all_tya2 varal = 
  case varal of
    [] => []
  | (var,arity) :: m => (type_of var,arity) :: all_tya2 m

fun all_tya term = 
  let varal = collapse_lowestarity (extract_var term) in
    erase_double all_tya2 varal
  end
  
(* on the result of all_tya *)
fun get_leafvtyl tyal =
  case tyal of
    [] => []
  | (ty,0) :: m => (ty,0) :: get_leafvtyl m
  | a :: m => leafvtypel m

fun get_nodevtyl tyal =
  case tyal of
    [] => []
  | (ty,0) :: m => nodevtypel m
  | (ty,arity) :: m => (ty,arity) :: get_nodevtyl m


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
