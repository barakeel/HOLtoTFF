structure blibSyntax :> blibSyntax =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype 
     
fun SYNTAX_ERR function message =
  HOL_ERR {origin_structure = "blibSyntax",
	         origin_function = function,
           message = message}

(* ACONV *)
fun is_member_aconv t l = is_member_eq aconv t l 
fun erase_aconv l = erase_double_eq aconv l 
fun merge_aconv terml = erase_aconv (List.concat terml)
 
(* TEST *) 
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun has_intty term = (type_of term = ``:int``)
fun is_var_or_const term = 
  is_var term orelse is_const term


(* QUANTIFIER *) 
fun strip_quant term =
  case structcomb term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise SYNTAX_ERR "strip_quant" "" 

fun namev_of_posint term =
  rm_last_n_char 1 (Arbintcore.toString (intSyntax.int_of_term term))

(* VAR *)
fun namev_of term = 
  case structterm term of
    Numeral => Int.toString (numSyntax.int_of_term term)
  | Integer => 
      if intSyntax.is_negated term
      then "$uminus(" ^ namev_of_posint (intSyntax.dest_negated term) ^ ")"
      else namev_of_posint term
  | Var => fst (dest_var term)
  | Const => fst (dest_const term)
  | Comb => raise SYNTAX_ERR "namev_of" "comb"
  | Abs => raise SYNTAX_ERR "namev_of" "abs" 
  
(* TERM *)   
fun strip_comb_n n term =
  if n = 0 then (term,[])
else 
  if n > 0 then let val (oper,arg) = dest_comb term in
                 let val (oper2,argl) = strip_comb_n (n-1) oper in
                   (oper2,argl @ [arg])
                 end end 
else 
  raise SYNTAX_ERR "" ""

fun get_arity term = length (snd (strip_comb term))

fun less_term (a,b) = Term.compare (a,b) = LESS

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

fun terml_to_string terml =
  case terml of
    [] => ""
  | [t] => (term_to_string t)
  | t :: m => (term_to_string t) ^ "``, ``" ^ (terml_to_string m)  
 
fun goal_to_string goal = 
  "([``" ^ terml_to_string (fst goal) ^ "``]" ^ 
  ", ``" ^ term_to_string (snd goal) ^ "``)"

(* Boolean argument *)
fun find_atoml term =
  case structterm term of
    Comb =>
    (
    case structcomb term of
      Forall => find_atoml_quant term 
    | Exists => find_atoml_quant term   
    | Conj => find_atoml_binop term 
    | Neg => find_atoml_unop term 
    | Imp_only => find_atoml_binop term
    | Disj => find_atoml_binop term 
    | _ => [term]
    )             
  | _ => [term]  
and find_atoml_quant term =
  let val (qbvl,t) = strip_quant term in find_atoml t end  
and find_atoml_binop term =
  find_atoml (lhand term) @ find_atoml (rand term)
and find_atoml_unop term =
  find_atoml (rand term)

fun has_boolarg_one term =
  let val argl = snd (strip_comb term) in
    exists has_boolty argl orelse
    exists has_boolarg_one argl
  end
           
fun has_boolarg term = 
  let val atoml = find_atoml term in
    exists has_boolarg_one atoml
  end

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  

fun has_boolarg_goal goal =
  let val l = (fst goal) @ [snd goal] in
    exists has_boolarg l
  end


end
