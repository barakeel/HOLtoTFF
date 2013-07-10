structure namevar :> namevar =
struct

open HolKernel numSyntax
     extractvar nametype  
     stringtools listtools tools mydatatype
     
fun NAMEVAR_ERR function message =
  HOL_ERR{origin_structure = "namevar",
          origin_function = function,
          message = message}


    


(* bound variable: bv *)
fun name_tff_bv term = name_tff "X" term
fun app_name_tff_bv term = (term,name_tff_bv term)

(* give a new name if the name is already used *)     
fun create_bvdict term =
  let val varacatl = extract_var term in
  let val bvl = map fst (get_bval varacatl) in 
  let val bvnamel = map app_name_tff_bv bvl in
    addnewnamel bvnamel []
  end end end

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" term
fun app_name_tff_fv term = (term,name_tff_fv term)

(* give a new name if the name is already used *)     
fun create_fvdict term =
  let val varacatl = extract_var term in
  let val fvl = map fst (get_fval varacatl) in 
  let val fvnamel = map app_name_tff_fv fvl in
    addnewnamel fvnamel []
  end end end

(* constant: c *)
(* don't need to monomorph = *)
(* this constant dict should be a little more complex *)
fun name_tff_c term = name_tff "c" term
fun app_name_tff_c term = (term,name_tff_c term)

fun create_cdict term =
  let val varacatl = extract_var term in
  let val cl = map fst (get_cal varacatl) in 
  let val cnamel = map app_name_tff_c cl in
    addnewnamel cnamel []
  end end end


(* Predicate *)
(* newname predicate variables type to "$o" *)
fun give_predicate_type tyadict term (v,a) = 
  let val tyname = lookup (type_of v,a) tyadict in
    if is_predicate_in v term 
    then ((v,a),change_to_predicatety tyname)
    else ((v,a),tyname)
  end

(* free variable arity type : fv a ty *)

(* link variables to their tff type *)
(* a bound variable should never be a predicate anyway *)
fun create_bvatydict term tyadict =
  let val varacatl = extract_var term in
  let val bval = get_bval (nullify_bval varacatl) in
    map (give_predicate_type tyadict term) bval
  end end

fun create_fvatydict term tyadict =
  let val varacatl = extract_var term in
  let val fval = collapse_lowestarity (get_fval varacatl) in
    map (give_predicate_type tyadict term) fval
  end end

fun create_catydict term tyadict =
  let val varacatl = extract_var term in
  let val cal = collapse_lowestarity (get_cal varacatl) in
    map (give_predicate_type tyadict term) cal
  end end
(* End Predicate *)     
   
  
end
  
