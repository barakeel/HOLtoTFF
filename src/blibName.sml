structure blibName :> blibName =
struct

open HolKernel Abbrev boolLib blibTools blibExtract

(* NAME TYPE *)
(* Gives an indicative name *)
fun pname_leaf ty = 
  if is_vartype ty then substring (dest_vartype ty, 1, size (dest_vartype ty) - 1)
  else alias "leaf" (fst (dest_type ty))

fun pname_sty ty = 
  if null (snd (gen_dest_type ty)) then pname_leaf ty
  else if "fun" = fst (gen_dest_type ty) then
    let val (str,l) = gen_dest_type ty in
      pname_sty (List.nth (l,0)) ^ "_F_" ^ pname_sty (List.nth (l,1))
    end 
  else 
    let val (str,tyl) = gen_dest_type ty in
      (alias "op" str) ^ "I" ^ (pname_styl tyl) ^ "I"
    end                  
and pname_styl tyl = concats "_" (map pname_sty tyl)
 
fun name_sty (ty,a) = 
  if ty = bool then "$o" else
  if String.size (pname_sty ty) > 40 then "toolong" else "ty_" ^ (pname_sty ty)

(* Create the type dictionary *)
fun create_tyadict term =
  let val tyanml = map (adj name_sty) (get_tyal term) in injectl tyanml [] end 

(* Naming coupound type *)
fun to_bool str = if str = "$o" then "ty_bool" else str

fun name_tyargl argl tyadict =
  concats " * " (map to_bool (map (inv assoc tyadict) argl))

fun name_tya_aux (argl,im) tyadict = 
  case argl of
    [] => assoc im tyadict
  | [tya] => assoc tya tyadict ^ " > " ^ assoc im tyadict
  | _ => "( " ^ name_tyargl argl tyadict ^ " )  > " ^ assoc im tyadict

fun name_tya (ty,arity) tyadict =
  let val (argl,im) = strip_type_n (ty,arity) in name_tya_aux (argl,im) tyadict end
   
(* NAME VAR *)
fun name_tff str name = if is_alphanum_ name then str ^ name else str

(* bound variable: bv *)
fun name_bv term = name_tff "X" (fst (dest_var term))
fun create_bvdict term = injectl (map (adj name_bv) (get_bvl term)) []

(* free variable: fv *)
fun name_fv term = name_tff "x" (fst (dest_var term))
fun create_fvdict term = injectl (map (adj name_fv) (free_vars term)) []

(* constant: c *)
fun name_c term = name_tff "c" (fst (dest_const term))
fun create_cdict term = injectl (map (adj name_c) (get_cl term)) []

(* small correction before printing *)
fun give_type tyadict term (v,a) = 
  let val tyname = name_tya (type_of v,a) tyadict in ((v,a),tyname) end
  
fun create_fvatydict term tyadict = map (give_type tyadict term) (get_fval term)
fun create_catydict term tyadict = map (give_type tyadict term) (get_cal term)
         

end
  
