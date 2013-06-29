structure namevar :> namevar =
struct

open HolKernel extractvar stringtools listtools mydatatype numSyntax

fun NAMEVAR_ERR function message =
  HOL_ERR{origin_structure = "namevar",
          origin_function = function,
          message = message}

(* tools *)  
fun name_of term = 
  case termstructure term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise NAMEVAR_ERR "name_of" "comb"
  | Abs => raise NAMEVAR_ERR "name_of" "abs"

fun name_tff startstr term =
  let val name = name_of term in 
    if is_alphanumor_ name
    then startstr ^ (name_of term)
    else startstr
  end
(* end tools*)
    
(* numeral *)
fun name_numeral term =  
  case termstructure term of
    Numeral => name_of term
  | _ => raise NAMEVAR_ERR "name_numeral" "not a numeral"

(* bound variable: bv *)
fun name_tff_bv term = name_tff "X" term
fun app_name_tff_bv term = (term,name_tff_bv term)

(* give a new name if the name is already used *)     
fun create_bvdict term =
  let val varacatl = extract_var term in
  let val bvl = map fst (get_bval varacatl) in 
  let val bvnamel = map app_name_tff_bv bvl in
    addrenamel bvnamel []
  end end end

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" term
fun app_name_tff_fv term = (term,name_tff_fv term)

(* give a new name if the name is already used *)     
fun create_fvdict term =
  let val varacatl = extract_var term in
  let val fvl = map fst (get_fval varacatl) in 
  let val fvnamel = map app_name_tff_fv fvl in
    addrenamel fvnamel []
  end end end

(* constant: c *)
fun name_tff_c term = name_tff "c" term
fun app_name_tff_c term = (term,name_tff_c term)

fun create_cdict term =
  let val varacatl = extract_var term in
  let val cl = map fst (get_cal varacatl) in 
  let val cnamel = map app_name_tff_c cl in
    addrenamel cnamel []
  end end end



end
  
