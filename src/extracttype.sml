structure extracttype :> extracttype =
struct

open HolKernel Abbrev boolLib listtools mydatatype extractvar extractterm

fun EXTRACTTYPE_ERR function message =
  HOL_ERR{origin_structure = "extracttype",
          origin_function = function,
          message = message}

fun all_type term = erase_double (map type_of (all_subterm term))

fun all_subtype_aux ty =
  case typecat ty of
    Booltype => [ty]
  | Numtype => [ty]
  | Alphatype => [ty]
  | Leaftype => [ty]
  | _ => let val (str,l) = dest_type ty in
           ty :: all_subtypel_aux l
         end
and all_subtypel_aux tyl = 
  list_merge (map all_subtype_aux tyl)
fun all_subtype term = all_subtypel_aux (all_type term)

fun all_leaftype_aux ty = 
  case typecat ty of
    Booltype => [ty]
  | Numtype => [ty]
  | Alphatype => [ty]
  | Leaftype => [ty]
  | _ => let val (str,l) = dest_type ty in
           all_leaftypel_aux l
         end
and all_leaftypel_aux tyl = 
  list_merge (map all_leaftype_aux tyl)
fun all_leaftype term = all_leaftypel_aux (all_type term)

fun all_vartype term = filter is_vartype (all_leaftypel_aux (all_type term))

(* WITH ARITY *)
fun vara_to_tya (var,a) = (type_of var,a)
fun all_tya_aux varal = map vara_to_tya varal

fun all_tya term = 
  let val varal = (map fst (get_varinfol term)) in
    erase_double (all_tya_aux varal)
  end
  
(* on the result of all_tya *)
fun is_in_simpletyal (ty,arity) = (arity = 0)
fun get_simpletyal term = filter is_in_simpletyal (all_tya term)

fun is_in_compoundtyal (ty,arity) = (arity > 0)
fun get_compoundtyal term  = filter is_in_compoundtyal (all_tya term)

fun strip_tya (ty,arity) = 
  case arity of
    0 => ([],(ty,0))
  | n => if n < 0 then raise EXTRACTTYPE_ERR "strip_tya" ""
         else
           let val (str,list) = dest_type ty in 
           let 
             val ty1 = hd list
             val ty2 = hd (tl list) 
           in
           let val resl = strip_tya (ty2,(n-1)) in
           let
             val argl = fst resl
             val image = snd resl 
           in
             ((ty1,0) :: argl,image) 
           end end end end
        

end
