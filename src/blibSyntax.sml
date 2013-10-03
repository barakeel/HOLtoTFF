structure blibSyntax :> blibSyntax =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools blibDatatype 
     
fun SYNTAX_ERR function message =
  HOL_ERR {origin_structure = "blibSyntax",
	         origin_function = function,
           message = message}

(* ACONV *)
fun is_member_aconv t l = is_member_eq aconv t l 
fun erase_double_aconv l = erase_double_eq aconv l 
 
(* TEST *) 
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun is_var_or_const term = 
  is_var term orelse is_const term
fun is_leaf term = 
  is_var term orelse is_const term orelse is_numeral term

(* QUANTIFIER *) 
fun strip_quant term =
  case connector term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise SYNTAX_ERR "strip_quant" "" 

fun bound_by_quant subterm term =
 let val (bvl,t) = strip_quant term in 
   free_in subterm t andalso not (free_in subterm term)
 end  

(* VAR *)
fun name_of term = 
  case termstructure term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise SYNTAX_ERR "name_of" "comb"
  | Abs => raise SYNTAX_ERR "name_of" "abs" 
  
(* TERM *)   
fun strip_comb_n (term,n) =
  if n = 0 then (term,[])
else 
  if n > 0 then let val (operator,arg) = dest_comb term in
                 let val (operator2,argl) = strip_comb_n (operator,n - 1) in
                   (operator2,argl @ [arg])
                 end end 
else 
  raise SYNTAX_ERR "" ""

fun get_arity term = length (snd (strip_comb term))

fun all_fosubterm_aux term = 
  case termstructure term of
    Numeral => [term]
  | Var => [term]  
  | Const => [term]
  | Comb => 
    (
    case connector term of
      Forall => all_fosubterm_aux_quant term
    | Exists => all_fosubterm_aux_quant term   
    | Conj => all_fosubterm_aux_binop term
    | Neg => all_fosubterm_aux_unop term
    | Imp_only => all_fosubterm_aux_binop term
    | Disj => all_fosubterm_aux_binop term
    | App => let val (operator,argl) = strip_comb term in
               term :: all_fosubterm_aux_list (operator :: argl)            
             end
    )  
  | Abs => term :: all_fosubterm_aux (snd (strip_abs term))
         
and all_fosubterm_aux_list terml = 
  erase_double_aconv (List.concat (map (all_fosubterm_aux) terml))
and all_fosubterm_aux_quant term = all_fosubterm_aux (snd (strip_quant term))
and all_fosubterm_aux_binop term = all_fosubterm_aux_list [lhand term,rand term] 
and all_fosubterm_aux_unop term = all_fosubterm_aux (rand term)

fun all_fosubterm term = 
  wrap "blibSyntax" "all_subterm" "" erase_double_aconv (all_fosubterm_aux term)

(* THM *)
fun only_hyp thm = 
  if length (hyp thm) = 1 then hd (hyp thm)
  else raise SYNTAX_ERR "only_hyp" "" 
 
fun is_refl eqth = (rhs (concl eqth) = lhs (concl eqth))
 
(* GOAL *)
fun only_hypg goal =
  if length (fst goal) = 1 then hd (fst goal)
  else raise SYNTAX_ERR "only_hypg" "" 
 
fun mk_goal thm = (hyp thm, concl thm)

fun is_member_aconv_rev a b = is_member_aconv b a 
fun is_subset l1 l2 = all (is_member_aconv_rev l2) l1

fun is_subset_goal goal1 goal2 = 
  aconv (snd goal1) (snd goal2) andalso
  is_subset (fst goal1) (fst goal2)
 
fun thm_test thm goal msg = 
  if is_subset_goal (mk_goal thm) goal then thm
  else raise SYNTAX_ERR msg ""
 
fun goal_to_string goal = 
  thm_to_string (mk_thm goal)

end
