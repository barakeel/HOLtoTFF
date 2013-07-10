structure tools :> tools =
struct

(*
load "listtools"; open listtools;
load "stringtools"; open stringtools;
*)

open HolKernel 
     stringtools listtools mydatatype


fun TOOLS_ERR function message =
    HOL_ERR{origin_structure = "tools",
	    origin_function = function,
            message = message}
 
type conv = Term.term -> Thm.thm 
 
(* test functions *) 
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun is_var_or_const term = is_var term orelse is_const term
(* end test functions *)
 
(* quantifier functions *) 
fun strip_quant term =
  case connector term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise TOOLS_ERR "strip_quant" "" 

fun bound_by_quant subterm term =
 let val (bvl,t) = strip_quant term in 
   free_in subterm t andalso not (free_in subterm term)
 end  
(* end quantifier *) 
 
(* term function *) 
fun name_of term = 
  case termstructure term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise TOOLS_ERR "name_of" "comb"
  | Abs => raise TOOLS_ERR "name_of" "abs"

fun name_tff startstr term =
  let val name = name_of term in 
    if is_alphanumor_ name
    then startstr ^ (name_of term)
    else startstr
  end

fun name_numeral term =  
  case termstructure term of
    Numeral => name_of term
  | _ => raise TOOLS_ERR "name_numeral" "not a numeral"
  
(* can't be used on a constant *)  
fun create_newvar var used = 
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
  
fun list_mk_var (strl,tyl) = map mk_var (combine (strl,tyl))

(* thm *)
fun rewrite_conv conv thm =
  let val goal = concl thm in
  let val eqthm = conv goal in
    EQ_MP eqthm thm
  end end     

fun rewrite_conv_hyp conv term thm =
  let val eqth1 = conv term in
  let val (lemma1,lemma2) = EQ_IMP_RULE eqth1 in
  let val lemma3 = UNDISCH lemma2 in
  let val th3 = PROVE_HYP lemma3 thm in
    th3
  end end end end 
  handle UNCHANGED => thm
   

(* some first order tools *)

(* consider = to be always = not <=> *)
fun find_atoml term =
  case termstructure term of
    Comb =>
    (
    case connector term of
      Forall => find_atoml_quant term 
    | Exists => find_atoml_quant term   
    | Conj => find_atoml_binop term 
    | Neg => find_atoml_unop term 
    | Imp_only => find_atoml_binop term
    | Disj => find_atoml_binop term 
    | App => [term]
    )             
  | _ => [term]  
and find_atoml_quant term =
  let val (qbvl,t) = strip_quant term in find_atoml t end  
and find_atoml_binop term =
  find_atoml (lhand term) @ find_atoml (rand term)
and find_atoml_unop term =
  find_atoml (rand term)
  
fun find_predicatel term = 
  let val atoml = find_atoml term in
    map fst (map strip_comb atoml)           
  end
  
fun is_predicate_in var term = 
  is_member var (find_predicatel term)

fun find_unpredicatel_aux atom =
  let val (operator,argl) = strip_comb atom in
    List.concat (map (find_terms is_var_or_const) argl)
  end      

fun find_unpredicatel term =
  let val atoml = find_atoml term in
   List.concat (map find_unpredicatel_aux atoml)
  end              
(* end first order tools *) 

(* newname bound variables *)











end