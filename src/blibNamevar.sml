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


(* All functions that returns "bool" are actually predicates returing "$o" *)
fun give_pred_type tyadict term (v,a) = 
  let val tyname = lookup (type_of v,a) tyadict in
    if success (last_n_char 6) tyname
    then
      if last_n_char 6 tyname = "> bool"
      then ((v,a), (rm_last_n_char 6 tyname) ^ ">$o")
      else ((v,a),tyname)
    else ((v,a),tyname)
  end

fun create_bvatydict term tyadict =
  let val bval = get_bval term in
    map (give_pred_type tyadict term) bval
  end 

fun create_fvatydict term tyadict =
  let val fval = get_fval term in
    map (give_pred_type tyadict term) fval
  end 

fun create_catydict term tyadict =
  let val cal = get_cal term in
    map (give_pred_type tyadict term) cal
  end 
(* end pred *)     
   
  
end
  
