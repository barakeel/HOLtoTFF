structure blibName :> blibName =
struct

open HolKernel Abbrev boolLib blibTools blibExtract intSyntax

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
  if ty = int_ty then "$int" 
  else if String.size (pname_sty ty) > 40 then "long" else "ty_" ^ (pname_sty ty)

(* Create the type dictionary *)
fun create_tyadict term =
  let val tyanml = map (adj name_sty) (get_tyal term) in injectl tyanml [] end 

(* NAME VAR *)
fun name_tff str name = 
   if String.substring (name,0,10) = "%%genvar%%" then str ^ "Abs"
   else alias (str ^ name) (str ^ "U")
   handle _ => alias (str ^ name) (str ^ "U")

(* bound variables *)
fun name_bv bv = name_tff "V" (fst (dest_var bv))
fun create_bvdict term = injectl (map (adj name_bv) (get_bvl term)) []

(* constants *)
fun name_c (c,a) = name_tff "c" (fst (dest_const c))
fun create_cadict term = injectl (map (adj name_c) (get_fvcal term)) []

end
  
