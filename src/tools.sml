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
    HOL_ERR {origin_structure = "tools",
	           origin_function = function,
             message = message}

(* BASIC *)  
fun repeat_n_fun n f x = 
  case n of
    0 => x
  | _ => if n < 0 
         then raise TOOLS_ERR "repeat_n_fun" ""  
         else f (repeat_n_fun (n - 1) f x)
         
(* ERROR HANDLING *)
fun success f x =
  (f x; true) handle _ => false
  
fun wrap s f m function x =
  function x               
  handle  
  HOL_ERR {origin_structure = s1, origin_function = f1, message = m1}
      => raise HOL_ERR {origin_structure = s ^ " - " ^ s1,
                        origin_function = f ^ " - " ^ f1,
                        message = m ^ " - " ^ m1}           
  | UNCHANGED => raise UNCHANGED
  | _ => raise HOL_ERR {origin_structure = s,
                        origin_function = f,
                        message = m}        

(* ACONV *)
fun is_member_term t l = is_member_eq aconv t l 
fun erase_double_term l = erase_double_eq aconv l 
 
(* TEST *) 
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun is_var_or_const term = is_var term orelse is_const term
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

(* NAME *)
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

(* DEFINED TFF CONSTANTS *)
(* (* bad hack NLIA *) prevent from adding  "*" *)
fun is_dc term = is_member (name_of term) ["=","+","-","<","<=",">",">="]
fun is_not_dc term = not (is_dc term)
fun is_dca (term,arity) = is_dc term andalso arity = 2
fun is_not_dca (term,arity) = not (is_dca (term,arity))
fun is_not_dcaty ((term,arity),str) = is_not_dca (term,arity)

(* TERM *)   
fun strip_comb_n (term,n) =
  if n = 0 then (term,[])
else 
  if n > 0 then let val (operator,arg) = dest_comb term in
                 let val (operator2,argl) = strip_comb_n (operator,n - 1) in
                   (operator2,argl @ [arg])
                 end end 
else 
  raise TOOLS_ERR "" ""

fun get_arity term = length (snd (strip_comb term))

(* THM *)
fun only_hyp thm = 
  if length (hyp thm) = 1 then hd (hyp thm)
  else raise TOOLS_ERR "only_hyp" "" 
 
fun is_refl eqth = (rhs (concl eqth) = lhs (concl eqth))
 
(* GOAL *)
fun only_hypg goal =
  if length (fst goal) = 1 then hd (fst goal)
  else raise TOOLS_ERR "only_hypg" "" 
 
fun mk_goal thm = (hyp thm, concl thm)

fun is_member_term_rev a b = is_member_term b a 
fun is_subset l1 l2 = all (is_member_term_rev l2) l1

fun is_subset_goal goal1 goal2 = 
  aconv (snd goal1) (snd goal2) andalso
  is_subset (fst goal1) (fst goal2)
 
fun thm_test thm goal msg = 
  if is_subset_goal (mk_goal thm) goal then thm
  else raise TOOLS_ERR msg ""
 
fun goal_to_string goal = thm_to_string (mk_thm goal)

(* CONV *)
fun repeat_n_conv n conv = 
  case n of
    0 => ALL_CONV
  | n => if n < 0 then raise TOOLS_ERR "repeat_n_conv" ""  
         else
           conv THENC repeat_n_conv (n - 1) conv

fun not_strip_exists_conv term =
  let val n = length (fst (strip_exists (dest_neg term))) in
    repeat_n_conv n (STRIP_QUANT_CONV NOT_EXISTS_CONV) term
  end  

fun strip_forall_not_conv term = 
  if is_forall term 
  then ((LAST_FORALL_CONV FORALL_NOT_CONV) THENC strip_forall_not_conv) term
  else raise UNCHANGED

(* RULE *)
fun conv_concl conv thm =
  let val conclt = concl thm in
  let val eqthm = conv conclt in
    EQ_MP eqthm thm
  end end     
  handle UNCHANGED => thm
  
fun conv_onehyp conv term thm =
  let val eqth1 = conv term in
  let val (lemma1,lemma2) = EQ_IMP_RULE eqth1 in
  let val lemma3 = UNDISCH lemma2 in
  let val th3 = PROVE_HYP lemma3 thm in
    th3
  end end end end 
  handle UNCHANGED => thm
 
fun conv_hypl conv terml thm = repeatchange (conv_onehyp conv) terml thm 
 
fun list_PROVE_HYP thml thm =
  case thml of
    [] => thm
  | th :: m => list_PROVE_HYP m (PROVE_HYP th thm)  

fun list_conj_hyp_rule thm =
  let val hyptl = hyp thm in
  let val t1 = list_mk_conj hyptl in
  let val thl = CONJ_LIST (length hyptl) (ASSUME t1) in
  let val th2 = list_PROVE_HYP thl thm in
    th2
  end end end end   

(* assume there is only one hypothesis *)
fun unconj_hyp_rule term thm =
  if is_conj term then
    let val th0 = ASSUME (lhand term) in
    let val th1 = ASSUME (rand term) in
    let val th2 = CONJ th0 th1 in
      PROVE_HYP th2 thm
    end end end 
  else raise TOOLS_ERR "unconj_hyp_rule" ""

(* hypl is a list of conj *)
fun list_unconj_hyp_rule hypl thm = repeatchange unconj_hyp_rule hypl thm
  
fun strip_conj_hyp_rule thm =
  case filter is_conj (hyp thm) of
    [] => thm
  | l => strip_conj_hyp_rule (list_unconj_hyp_rule l thm)

fun list_AP_THM thm terml =
  case terml of
    [] => thm 
  | t :: m => list_AP_THM (AP_THM thm t) m 


(* input is an equality *)
fun list_FUN_EQ_CONV vl term =
  case vl of
    [] => raise UNCHANGED
  | [v] => X_FUN_EQ_CONV v term
  | v :: m => ((X_FUN_EQ_CONV v) THENC 
              (STRIP_QUANT_CONV (list_FUN_EQ_CONV m))) 
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

fun list_TRANS eqthml =
  case eqthml of
    [] => raise TOOLS_ERR "list_TRANS" "no argument"
  | [eqthm] => eqthm
  | eqthm :: m => TRANS eqthm (list_TRANS m) 
    
(* EXTRACT TERM *)
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
         
and all_subterm_aux_list terml = 
  erase_double_term (List.concat (map (all_subterm_aux) terml))
and all_subterm_aux_quant term = all_subterm_aux (snd (strip_quant term))
and all_subterm_aux_binop term = all_subterm_aux_list [lhand term,rand term] 
and all_subterm_aux_unop term = all_subterm_aux (rand term)

fun all_subterm term = erase_double_term (all_subterm_aux term)
(* end *)

(* extract term type *)
fun all_type term = erase_double (map type_of (all_subterm term))

fun all_subtype_aux ty =
  case typecat ty of
    Booltype => [ty]
  | Numtype => [ty]
  | Alphatype => [ty]
  | Leaftype => [ty]
  | _ => let val (str,l) = dest_type ty in
           ty :: all_subtypel_aux l
         end
and all_subtypel_aux tyl = 
  erase_double (List.concat (map all_subtype_aux tyl))
fun all_subtype term = all_subtypel_aux (all_type term)

fun all_leaftype_aux ty = 
  case typecat ty of
    Booltype => [ty]
  | Numtype => [ty]
  | Alphatype => [ty]
  | Leaftype => [ty]
  | _ => let val (str,l) = dest_type ty in
           all_leaftypel_aux l
         end
and all_leaftypel_aux tyl = 
  erase_double (List.concat (map all_leaftype_aux tyl))
fun all_leaftype term = all_leaftypel_aux (all_type term)

fun all_vartype term = filter is_vartype (all_leaftypel_aux (all_type term))

(* test 
all_vartype ``(f a = b) /\ (c=0)``;
all_leaftype (type_of term);
*)
(* MOSTLY USED FOR BOOLEANS *)

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

fun find_pred_one atom =
  let val (operator,argl) = strip_comb atom in
    if is_dc operator andalso length argl = 2 
    (* prevent the dc to be seen as predicates *)
    then []
    else [operator]
  end
  
fun find_pred term = 
  let val atoml = find_atoml term in
    List.concat (map find_pred_one atoml)          
  end 

fun is_pred_in var term = 
  is_member_term var (find_pred term)

fun find_unpred_arg arg =
  filter is_var_or_const (all_subterm arg)

fun find_unpred_aux atom =
  let val (operator,argl) = strip_comb atom in
    erase_double_term (List.concat (map (find_unpred_arg) argl))
  end      

fun find_unpred term =
  let val atoml = find_atoml term in
   erase_double_term (List.concat (map find_unpred_aux atoml))
  end              

fun has_boolarg term = not (null (filter has_boolty (find_unpred term)))

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  

fun has_boolarg_goal goal =
  let val l = (fst goal) @ [snd goal] in
    exists has_boolarg l
  end

end