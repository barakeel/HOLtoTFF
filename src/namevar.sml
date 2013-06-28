structure namevar :> namevar =
struct

open HolKernel extract_var stringtools listtools mydatatype numSyntax

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
  | Comb => raise MONOMORPH_ERR "name_of" "comb"
  | Abs => raise MONOMORPH_ERR "name_of" "abs"

fun name_tff startstr term =
  let val name = name_of bv in 
    if is_alphanumor_ name
    then startstr ^ (name_of bv)
    else startstr
  end

fun name_new name used =
  let val nameref = ref name in 
  let val nref = ref 0 in
    while is_member (!nameref) used
    do
      (nameref := (!nameref) ^ (Int.toString (!nref));
       nref := (!nref) + 1) 
  end end

(* all my dict are injective dict this way *)
fun add_to_dict (key,name) dict =
  let val newname = name_new name (map snd dict) in
    add_entry (key,newname) dict
  end  

fun addl_to_dict termnamedl dict =
  case terml of
    [] => []
  | termnamed :: m => addl_to_dict m (add_to_dict termnamed dict)
(* end tools*)
    
(* numeral *)
fun name_numeral term =  
  case termstructure term of
    Numeral => name_of term
  | _ => raise NAMEVAR_ERR "name_numeral" "not a numeral"

(* bound variable:bv *)
fun name_tff_bv term = name_tff "X" term
fun app_name_tff_bv term = (name,name_tff_bv term)

(* give a new name if the name is already used *)     
fun create_bvdict term =
  let val varacatl = extract_var term in
  let val bvl = map fst (get_bval varacatl) in 
  let val bvnamed = map app_name_tff_bv bvl
    addl_to_bvdict bvnamed []
  end end

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" term
fun app_name_tff_fv term = (name,name_tff_fv term)

(* give a new name if the name is already used *)     
fun create_fvdict term =
  let val varacatl = extract_var term in
  let val fvl = map fst (get_fval varacatl) in 
  let val fvnamed = map app_name_tff_fv fvl
    addl_to_fvdict fvnamed []
  end end

(* constant: c *)
fun name_tff_c term = name_tff "c" term
fun app_name_tff_c term = (name,name_tff_c term)

fun create_cdict term =
  let val varacatl = extract_var term in
  let val cl = map fst (get_cal varacatl) in 
  let val cnamed = map app_name_tff_c cl
    addl_to_cdict cnamed []
  end end



end
  
