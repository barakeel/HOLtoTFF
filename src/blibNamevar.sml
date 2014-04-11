structure blibNamevar :> blibNamevar =
struct

open HolKernel Abbrev boolLib blibExtractvar blibNametype blibBtools 

fun name_tff str name = if is_alphanum_ name then str ^ name else str

(* bound variable: bv *)
fun name_tff_bv term = name_tff "X" (fst (dest_var term))
fun app_name_tff_bv term = (term,name_tff_bv term)
fun create_bvdict term =
  add_newnamel (map app_name_tff_bv (get_bvl term)) []

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" (fst (dest_var term))
fun app_name_tff_fv term = (term,name_tff_fv term)
fun create_fvdict term =
  add_newnamel (map app_name_tff_bv (get_fvl term)) []

(* constant: c *)
fun name_tff_c term = name_tff "c" (fst (dest_const term))
fun app_name_tff_c term = (term,name_tff_c term)
fun create_cdict term =
  add_newnamel (map app_name_tff_bv (get_cl term)) []

(* small correction before printing *)
fun give_type tyadict term (v,a) = 
  (* variables *)
  let val atoml = find_atoml term in
    if is_member v atoml then ((v,a),"$o") else
  (* functions *)  
    let val tyname = name_tya (type_of v,a) tyadict in
      if last_n_char 9 tyname = "> ty_bool"
      then ((v,a), (rm_last_n_char 9 tyname) ^ "> $o")
      else ((v,a),tyname)
      handle _ => ((v,a),tyname)
    end
  end
  
fun create_fvatydict term tyadict =
  map (give_type tyadict term) (get_fval term)
fun create_catydict term tyadict =
  map (give_type tyadict term) (get_cal term)
         
end
  
