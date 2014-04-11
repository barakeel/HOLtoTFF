structure blibNametype :> blibNametype =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype 
     blibExtractvar blibFreshvar blibExtracttype 

(* Extract the types *)
fun vara_to_tya (var,a) = (type_of var,a)

fun all_tya term = 
  let 
  let val varal = (map fst (info_varl term)) in
    erase_double (map vara_to_tya varal)
  end
  
fun is_sty (ty,arity) = (arity = 0)
fun get_styal term = filter is_sty (all_tya term)

fun is_cty (ty,arity) = (arity > 0)
fun get_ctyal term  = filter is_cty (all_tya term)

fun strip_type_n (ty,a) = 
  if a = 0 then ([],(ty,0))
  else if a > 0 then
    let val (str,l) = dest_type ty in
    let val (ty1,ty2) = (List.nth (l,0),List.nth (l,1)) in
    let val resl = strip_type_n (ty2,(a-1)) in
    let val (argl,im) = (fst resl,snd resl) in
      ((ty1,0) :: argl,im) 
    end end end end
  else raise B_ERR "strip_type_n" "negative"

fun flatten_ctya ctya = 
  let val (im,arg) = strip_type_n ctya in im :: arg end
fun flatten_ctyal ctyal = merge (map flatten_ctya ctyal)

(* Gives an indicative name *)
fun pname_leaf ty = 
  if is_tyvar ty then substring (dest_vartype ty, 1, size (dest_vartype ty) - 1)
  else alias (fst (dest_type ty))

fun pname_sty ty = 
  if [] = snd (dest_type ty) then pname_leaf ty
  else if "fun" = snd (dest_type ty) then
    let val (str,l) = dest_type ty in
      pname_sty (List.nth l 0) ^ "_F_" ^ pname_sty (List.nth l 1)
    end 
  else 
    let val (str,tyl) = dest_type ty in
      (alias "op" str) ^ "I" ^ (pname_styl tyl) ^ "I"
    end                  
and pname_styl tyl = concats "_" (map pname_sty ty)
 
fun name_sty ty = 
  if String.size (pname_sty ty) > 40 then "toolong" else "ty_" ^ (pname_sty ty)

(* Create the type dictionary *)
fun create_tyadict term =
  let val styal = get_styal term in
  let val cstyal = merge (map flatten_ctya (get_ctyal term)) in
  let val tyanml = map (adj name_sty) (styal @ ctyal) in 
    insertList tyanml []
  end end end

(* Naming coupound type *)
fun name_tyargl argl tyadict =
  concats " * " (map (inv lookup tyadict) argl
  
fun name_cty (argl,im) tyadict = 
  case argl of
    [] => lookup im tyadict
  | [tya] => lookup tya tyadict ^ " > " ^ lookup im tyadict
  | _ => "( " ^ name_tyargl argl tyadict ^ " )  > " ^ lookup im tyadict

fun name_tya (ty,arity) tyadict =
  let val (argl,im) = strip_type_n (ty,arity) in name_cty (argl,im) tyadict end
   
end
  
