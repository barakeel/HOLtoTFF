structure blibExtracttype :> blibExtracttype =
struct

open HolKernel Abbrev boolLib 
     blibBtools
     blibDatatype blibExtractvar

fun EXTRACTTYPE_ERR function message =
  HOL_ERR{origin_structure = "blibExtracttype",
          origin_function = function,
          message = message}

(* WITH ARITY *)
fun vara_to_tya (var,a) = (type_of var,a)
fun all_tya_aux varal = map vara_to_tya varal

fun all_tya term = 
  let val varal = (map fst (info_varl term)) in
    erase_double (all_tya_aux varal)
  end
  
(* on the result of all_tya *)
fun is_in_simpletyal (ty,arity) = (arity = 0)
fun get_simpletyal term = filter is_in_simpletyal (all_tya term)

fun is_in_compoundtyal (ty,arity) = (arity > 0)
fun get_compoundtyal term  = filter is_in_compoundtyal (all_tya term)

fun strip_type_n (ty,arity) = 
  case arity of
    0 => ([],(ty,0))
  | n => if n < 0 then raise EXTRACTTYPE_ERR "strip_type_n" ""
         else
           let val (str,list) = dest_type ty in 
           let 
             val ty1 = hd list
             val ty2 = hd (tl list) 
           in
           let val resl = strip_type_n (ty2,(n-1)) in
           let
             val argl = fst resl
             val image = snd resl 
           in
             ((ty1,0) :: argl,image) 
           end end end end
        

end
