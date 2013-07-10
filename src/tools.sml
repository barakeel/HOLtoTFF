structure tools :> tools =
struct

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
fun list_mk_var (strl,tyl) = map mk_var (combine (strl,tyl))

(* thm *)
fun rewrite_conv conv thm =
  let val goal = concl thm in
  let val eqthm = conv goal in
    EQ_MP eqthm thm
  end end     

(* some first order tools *)


fun find_atoml term tyadict =
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
    | App => 
      (
        case nodeconst term of
        Eq => if lookup (type_of (lhs term),0) tyadict  = "$o" tyadict andalso 
                 lookup (type_of (rhs term),0) tyadict  = "$o" 
              then find_atoml_binop term
              else [term]     
      | _ => [term]
      )
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
(* end first order tools *) 


end