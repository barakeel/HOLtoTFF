structure blibNamevar :> blibNamevar =
struct

open HolKernel Abbrev boolLib numSyntax
     blibExtractvar blibFreshvar blibNametype  
     blibBtools blibDatatype
     blibSyntax blibTffsyntax blibPredicate
     
fun NAMEVAR_ERR function message =
  HOL_ERR{origin_structure = "blibNamevar",
          origin_function = function,
          message = message}

(* bound variable: bv *)
fun name_tff_bv term = name_tff "X" term
fun app_name_tff_bv term = (term,name_tff_bv term)

(* give a new name if the name is already used *)     
fun create_bvdict term =
  let val bvl = get_bvl term in 
  let val bvnamel = map app_name_tff_bv bvl in
    add_newnamel bvnamel []
  end end 

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" term
fun app_name_tff_fv term = (term,name_tff_fv term)
  
fun create_fvdict term =
  let val fvl = get_fvl term in 
  let val fvnamel = map app_name_tff_fv fvl in
    add_newnamel fvnamel []
  end end 

(* constant: c *)
fun name_tff_c term = name_tff "c" term
fun app_name_tff_c term = (term,name_tff_c term)

fun create_cdict term =
  let val cl = get_cl term in 
  let val cnamel = map app_name_tff_c cl in
    add_newnamel cnamel []
  end end


(* pred *)
(* "bool" to "$o" *)
fun give_pred_type tyadict term (v,a) = 
  let val tyname = lookup (type_of v,a) tyadict in
    if is_pred_in v term 
    then ((v,a),bool_to_o_type tyname)
    else ((v,a),tyname)
  end

fun give_predc_type tyadict term (c,a) = 
  let val tyname = lookup (type_of c,a) tyadict in
    if is_pred_in c term 
    then ((c,a),bool_to_o_type tyname)
    else ((c,a),tyname)
  end

(* link variables to their tff type *)
fun add_bvty tyadict (bv,a) = ((bv,a),lookup (type_of bv,a) tyadict)

fun create_bvatydict term tyadict =
  let val bval = get_bval term in
    map (add_bvty tyadict) bval
  end 

fun create_fvatydict term tyadict =
  let val fval = get_fval term in
    map (give_pred_type tyadict term) fval
  end 

fun create_catydict term tyadict =
  let val cal = get_cal term in
    map (give_predc_type tyadict term) cal
  end 
(* end pred *)     
   
  
end
  
