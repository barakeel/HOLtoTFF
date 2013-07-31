structure tools :> tools =
struct

(*
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "mydatatype"; open mydatatype;
*)

open HolKernel Abbrev boolLib numSyntax
     stringtools listtools mydatatype


fun TOOLS_ERR function message =
    HOL_ERR{origin_structure = "tools",
	    origin_function = function,
            message = message}

 (* ACONV *)
fun is_member_aconv t l = is_member_eq aconv t l 
fun erase_double_aconv l = erase_double_eq aconv l 
 
local fun is_equal (t1,a1) (t2,a2) = aconv t1 t2 andalso a1 = a2
in
fun is_member_aconv_arity (t,a) termal = is_member_eq is_equal (t,a) termal
fun erase_double_aconv_arity termal = erase_double_eq is_equal termal
end

(* TEST *) 
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun is_var_or_const term = is_var term orelse is_const term
fun is_logical term =
  is_conj term orelse
  is_disj term orelse   
  is_neg term orelse   
  is_imp_only term orelse
  is_forall term orelse  
  is_exists term orelse  
  is_exists1 term orelse
  is_cond term 
fun is_new_axiom terml axiom = not (is_member (concl axiom) terml)
fun is_not_var term = not (is_var term)  
  

  
(* QUANTIFIER *) 
fun strip_quant term =
  case connector term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise TOOLS_ERR "strip_quant" "" 

fun bound_by_quant subterm term =
 let val (bvl,t) = strip_quant term in 
   free_in subterm t andalso not (free_in subterm term)
 end  
(* TYPE *)
 
(* TERM *) 
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
fun list_mk_var (strl,tyl) = map mk_var (combine (strl,tyl))

fun strip_comb_n (term,n) =
  if n = 0 then (term,[])
else 
  if n > 0 then let val (operator,arg) = dest_comb term in
                 let val (operator2,argl) = strip_comb_n (operator,n - 1) in
                   (operator2,argl @ [arg])
                 end end 
else 
  raise TOOLS_ERR "" ""

(* ARITY *)
fun get_arity term = length (snd (strip_comb term))

fun get_lowestarity (term,arity) termal =
  case termal of
    [] => arity
  | (t,a) :: m => if term = t 
                  then 
                    if a < arity 
                    then get_lowestarity (term,a) m
                    else get_lowestarity (term,arity) m 
                  else get_lowestarity (term,arity) m     
;

  
fun collapse_lowestarity2 varal varalfix=
  case varal of
    [] => []
  | (var,arity) :: m => 
    let val lowestarity = get_lowestarity (var,arity) varalfix in
      (var,lowestarity) :: collapse_lowestarity2  m varalfix
    end
  
fun collapse_lowestarity varal = 
  erase_double (collapse_lowestarity2 varal varal)
  
(* CONV *)
fun repeat_n_conv n conv = 
  case n of
    0 => ALL_CONV
  | n => if n < 0 then raise TOOLS_ERR "repeat_n_conv" ""  
         else
           conv THENC repeat_n_conv (n - 1) conv

fun not_exists_list_conv term =
  let val n = length (fst (strip_exists (dest_neg term))) in
    (NOT_EXISTS_CONV THENC 
    (repeat_n_conv (n - 1) (STRIP_QUANT_CONV NOT_EXISTS_CONV)))
    term
  end  

(* RULE *)
fun conv_concl conv thm =
  let val conclt = concl thm in
  let val eqthm = conv conclt in
    EQ_MP eqthm thm
  end end     
  handle UNCHANGED => thm
  
fun conv_hyp conv term thm =
  let val eqth1 = conv term in
  let val (lemma1,lemma2) = EQ_IMP_RULE eqth1 in
  let val lemma3 = UNDISCH lemma2 in
  let val th3 = PROVE_HYP lemma3 thm in
    th3
  end end end end 
  handle UNCHANGED => thm
 
fun conv_hypl conv terml thm = repeatchange (conv_hyp conv) terml thm 
 
fun list_prove_hyp thml thm =
  case thml of
    [] => thm
  | th :: m => list_prove_hyp m (PROVE_HYP th thm)  

fun list_conj_hyp thm =
  let val hyptl = hyp thm in
  let val t1 = list_mk_conj hyptl in
  let val thl = CONJ_LIST (length hyptl) (ASSUME t1) in
  let val th2 = list_prove_hyp thl thm in
    th2
  end end end end   

(* assume there is only one hypothesis *)
fun unconj_hyp term thm =
  if is_conj term then
    let val th0 = ASSUME (lhand term) in
    let val th1 = ASSUME (rand term) in
    let val th2 = CONJ th0 th1 in
      PROVE_HYP th2 thm
    end end end 
  else raise TOOLS_ERR "unconj_hyp" ""

(* hypl is a list of conj *)
fun list_unconj_hyp hypl thm = repeatchange unconj_hyp hypl thm
  
fun strip_conj_hyp thm =
  case filter is_conj (hyp thm) of
    [] => thm
  | l => strip_conj_hyp (list_unconj_hyp l thm)

fun list_ap_thm thm terml =
  case terml of
    [] => thm 
  | t :: m => list_ap_thm (AP_THM thm t) m 



(* input is an equality *)
fun list_fun_eq_conv vl term =
  case vl of
    [] => raise UNCHANGED
  | [v] => X_FUN_EQ_CONV v term
  | v :: m => ((X_FUN_EQ_CONV v) THENC 
              (STRIP_QUANT_CONV (list_fun_eq_conv m))) 
              term 
   
fun repeat_rule n rule thm =   
  case n of
    0 => thm
  | _ => if n < 0 then raise TOOLS_ERR "repeat_rule" ""
         else rule (repeat_rule (n - 1) rule thm) 
         
fun EXTL bvl thm =
  case rev bvl of
    [] => thm
  | bv :: m => let val th0 = SPECL bvl thm in
                 EXTL (rev m) ( GENL(rev m) (EXT (GEN bv th0)) )  
               end             
              
(* extract term *)
fun all_subterm_aux term = 
  case termstructure term of
    Numeral => [term]
  | Var => [term]  
  | Const => [term]
  | Comb => 
    (
    case connector term of
      Forall => all_subterm_aux_quant term
    | Exists => all_subterm_aux_quant term   
    | Conj => all_subterm_aux_binop term
    | Neg => all_subterm_aux_unop term
    | Imp_only => all_subterm_aux_binop term
    | Disj => all_subterm_aux_binop term
    | App => let val (operator,argl) = strip_comb term in
               term :: all_subterm_aux_list (operator :: argl)            
             end
    )  
  | Abs => term :: all_subterm_aux (snd (strip_abs term))
         
and all_subterm_aux_list terml = List.concat (map (all_subterm_aux) terml)
and all_subterm_aux_quant term = all_subterm_aux (snd (strip_quant term))
and all_subterm_aux_binop term = all_subterm_aux_list [lhand term,rand term] 
and all_subterm_aux_unop term = all_subterm_aux (rand term)

fun all_subterm term = erase_double (all_subterm_aux term)
(* end *)

(* extract term type *)
fun all_type term = erase_double (map type_of (all_subterm term))

fun all_leafty ty =  
  case typecat ty of
    Booltype => [ty]
  | Numtype => [ty]
  | Alphatype => [ty]
  | Leaftype => [ty]
  | _ => let val (str,l) = dest_type ty in
           all_leaftyl l
         end  
and all_leaftyl tyl = List.concat (map all_leafty tyl)   

fun all_vartype term = filter is_vartype (all_leafty (type_of term))

(* FIRST ORDER *)
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

fun find_unpredicate_arg arg =
  filter is_var_or_const (all_subterm arg)

fun find_unpredicatel_aux atom =
  let val (operator,argl) = strip_comb atom in
    List.concat (map (find_unpredicate_arg) argl)
  end      

fun find_unpredicatel term =
  let val atoml = find_atoml term in
   List.concat (map find_unpredicatel_aux atoml)
  end              

fun has_boolarg term = not (null (filter has_boolty (find_unpredicatel term)))

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  




end