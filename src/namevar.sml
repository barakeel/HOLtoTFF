structure namevar :> namevar =
struct

open HolKernel Abbrev boolLib numSyntax
     extractvar nametype  
     stringtools listtools tools mydatatype
     
fun NAMEVAR_ERR function message =
  HOL_ERR{origin_structure = "namevar",
          origin_function = function,
          message = message}

(* create a fresh name *)
fun create_newname_aux name used =    
  let val newname = ref name in
  let val n = ref 0 in
    (
    while is_member (!newname) used do
    (
    n := (!n) + 1;
    newname := name ^ (Int.toString (!n))
    );
    !newname
    )
  end end
 
fun create_newname name term = 
  create_newname_aux name (map name_of (all_var term)) 
  
fun create_newname_thm name thm = 
  create_newname_aux name (map name_of (all_var_thm thm))
  
   
(* create a fresh variable *)
fun create_newvar_aux var used = 
  let val ty = type_of var in
  let val name = fst (dest_var var) in
  let val n = ref 0 in
  let val var = ref (mk_var (name,ty)) in
    (
    while is_member (!var) used do
      ( n := (!n) + 1;
        var :=  mk_var (name ^ (Int.toString (!n)),ty) ) 
    ;
    (!var)
    )    
  end end end end 
  
fun create_newvar var term = create_newvar_aux var (all_var term)  
fun create_newvar_thm var thm = create_newvar_aux var (all_var_thm thm)

fun create_newvarl_aux varl used =
  case varl of
    [] => []
  | v :: m => let val newv = create_newvar_aux v used in
                create_newvar_aux v used :: create_newvarl_aux m (v :: used)
              end  

fun create_newvarl varl term = create_newvarl_aux varl (all_var term)   
fun create_newvarl_thm varl thm = create_newvarl_aux varl (all_var_thm thm)

  
  
  
(* bound variable: bv *)
fun name_tff_bv term = name_tff "X" term
fun app_name_tff_bv term = (term,name_tff_bv term)

(* give a new name if the name is already used *)     
fun create_bvdict term =
  let val bvl = get_bvl term in 
  let val bvnamel = map app_name_tff_bv bvl in
    addnewnamel bvnamel []
  end end 

(* free variable: fv *)
fun name_tff_fv term = name_tff "x" term
fun app_name_tff_fv term = (term,name_tff_fv term)
  
fun create_fvdict term =
  let val fvl = get_fvl term in 
  let val fvnamel = map app_name_tff_fv fvl in
    addnewnamel fvnamel []
  end end 

(* constant: c *)
fun name_tff_c term = name_tff "c" term
fun app_name_tff_c term = (term,name_tff_c term)

fun create_cdict term =
  let val cl = get_cl term in 
  let val cnamel = map app_name_tff_c cl in
    addnewnamel cnamel []
  end end


(* predicate *)
(* name (predicate variable type) to "$o" *)
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
  let val bval = get_bval term in
    map (give_predicate_type tyadict term) bval
  end 

fun create_fvatydict term tyadict =
  let val fval = get_fval term in
    map (give_predicate_type tyadict term) fval
  end 

fun create_catydict term tyadict =
  let val cal = get_cal term in
    map (give_predicate_type tyadict term) cal
  end 
(* End Predicate *)     
   
  
end
  
