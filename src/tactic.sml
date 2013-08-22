structure tactic :> tactic =
struct

open HolKernel Abbrev boolLib
     stringtools listtools tools mydatatype 
     extractvar extracttype freshvar higherorder
     conv clausesettools printtools


fun TACTIC_ERR function message =
    HOL_ERR {origin_structure = "tactic",
	           origin_function = function,
             message = message}

(************ TOOLS ***************)
(* TAC BUILDER *)
fun mk_tac1 goalbuilder valbuilder goal =
  let val goal_list = [goalbuilder goal] in
  let val validation = fn [thm] => valbuilder goal thm  
                       | _     => raise TACTIC_ERR "mk_tac1" ""           
  in
     (goal_list,validation)
  end end

(* CONV_HYP_TAC *) 
fun conv_hyp conv goal =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val terml = erase_double_term (map (rhs o concl) eqthl) in
    (terml,snd goal)
  end end
  
fun conv_hyp_val conv goal thm =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val allhyp = List.concat (map hyp eqthl) in
    if null allhyp then 
      let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
      let val th0 = list_PROVE_HYP lemmal thm in
        thm_test th0 goal "conv_hyp_val"
      end end
    else raise TACTIC_ERR "conv_hyp_val" "no hypothesis allowed"
  end end 
   
fun CONV_HYP_TAC conv goal =
  mk_tac1 (conv_hyp conv) (conv_hyp_val conv) goal

(* list_ASSUME_TAC *)
fun list_ASSUME_TAC_w thml goal =
  case thml of
    [] => ALL_TAC goal
  | thm :: m => ((ASSUME_TAC thm) THEN (list_ASSUME_TAC_w m)) goal
fun list_ASSUME_TAC thml goal =     
  wrap "tactic" "list_ASSUME_TAC" "" list_ASSUME_TAC_w thml goal
  
(*********** PROBLEM_TO_GOAL_TAC ************)
  (* CONJ_HYP_TAC *)
fun conj_hyp goal = 
  ([list_mk_conj (fst goal)],snd goal)
  
fun conj_hyp_val goal thm =
  let val lemma = LIST_CONJ (map ASSUME (fst goal)) in
  let val th1 = PROVE_HYP lemma thm in
    thm_test th1 goal "conj_hyp_val"
  end end

fun CONJ_HYP_TAC goal = 
  if null (fst goal) then ALL_TAC goal 
  else mk_tac1 conj_hyp conj_hyp_val goal
  
  (* ASSUME_THML_TAC *)
fun thml_axiom thml = LIST_CONJ (map (GEN_ALL o DISCH_ALL) thml)

fun ASSUME_THML_TAC thml goal =
  (if null thml then ALL_TAC else ASSUME_TAC (thml_axiom thml)) goal

  (* *)
fun PROBLEM_TO_GOAL_TAC_w thml goal =
  (
  CONJ_HYP_TAC THEN
  CCONTR_TAC THEN
  CONJ_HYP_TAC THEN
  (ASSUME_THML_TAC thml) THEN
  CONJ_HYP_TAC
  )
  goal
fun PROBLEM_TO_GOAL_TAC thml goal = 
  wrap "tactic" "PROBLEM_TO_GOAL_TAC" "" (PROBLEM_TO_GOAL_TAC_w thml) goal

(*********** BEAGLE_CONV_TAC **********)   
fun CNF_CONV_TAC goal = 
  wrap "tactic" "CNF_CONV_TAC" "" (CONV_HYP_TAC normalForms.CNF_CONV) goal

fun FUN_CONV_TAC_w goal = 
  let val eqth = (QCONV fun_conv) (only_hypg goal) in
    (flag_update funflag (not (is_refl eqth));
     CONV_HYP_TAC fun_conv goal)
  end
fun FUN_CONV_TAC goal = 
  wrap "tactic" "FUN_CONV_TAC" "" FUN_CONV_TAC_w goal  

fun BOOL_CONV_TAC_w goal = 
  let val eqth = (QCONV bool_conv) (only_hypg goal) in
    (flag_update boolflag (not (is_refl eqth));
     CONV_HYP_TAC bool_conv goal)
  end
fun BOOL_CONV_TAC goal = 
  wrap "tactic" "BOOL_CONV_TAC" "" BOOL_CONV_TAC_w goal 

fun NUM_CONV_TAC_w goal =
  let val eqthl = map (QCONV num_conv) (fst goal) in
    (flag_update numflag (not (all is_refl eqthl));
     CONV_HYP_TAC (QCONV (num_conv THENC normalForms.CNF_CONV)) goal)
  end
fun NUM_CONV_TAC goal =
  wrap "tactic" "NUM_CONV_TAC" "" NUM_CONV_TAC_w goal


fun BEAGLE_CONV_TAC_w goal = 
  (
  CNF_CONV_TAC THEN
  FUN_CONV_TAC THEN
  CNF_CONV_TAC THEN
  BOOL_CONV_TAC THEN
  CNF_CONV_TAC THEN
  NUM_CONV_TAC THEN
  CNF_CONV_TAC
  )
  goal
fun BEAGLE_CONV_TAC goal = 
  wrap "tactic" "BEAGLE_CONV_TAC" "" BEAGLE_CONV_TAC_w goal 


(*********** BEAGLE_CLAUSE_SET_TAC **********)
(* ERASE_EXISTS_TAC *)
fun erase_exists_val goal thm =
  let val (bvl,t) = strip_exists (only_hypg goal) in
  let val th1 = DISCH (only_hyp thm) thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL bvl th2 in
  let val th4 = conv_concl (QCONV strip_forall_not_conv) th3 in
  let val th5 = NOT_ELIM th4 in
  let val th6 = UNDISCH th5 in
    thm_test th6 goal "erase_exists_val"
  end end end end end 
  end end
 
fun erase_exists goal =
  let val (bvl,t) = strip_exists (only_hypg goal) in 
    ([t],snd goal)
  end 
 
fun ERASE_EXISTS_TAC goal =
  wrap "tactic" "ERASE_EXISTS_TAC" ""
    (mk_tac1 erase_exists erase_exists_val) goal
 
(* FORALL_CONJUNCTS_TAC *)
fun FORALL_CONJUNCTS_TAC goal = 
  wrap "tactic" "FORALL_CONJUNCTS_TAC" ""
    (CONV_HYP_TAC forall_conjuncts_conv) goal

(* STRIP_CONJ_ONLY_HYP_TAC *)
fun strip_conj_only_hyp goal =  
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
    (terml,snd goal)
  end
  
fun strip_conj_only_hyp_val goal thm =
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
  let val thml = CONJUNCTS (ASSUME (only_hypg goal)) in
    list_PROVE_HYP thml thm
  end end
      
fun STRIP_CONJ_ONLY_HYP_TAC goal =
  wrap "tactic" "STRIP_CONJ_ONLY_HYP_TAC" ""
    (mk_tac1 strip_conj_only_hyp strip_conj_only_hyp_val) goal
  
(* ERASE_FORALL_TAC *)
fun ERASE_FORALL_TAC goal = 
  wrap "tactic" "ERASE_FORALL" ""
    (CONV_HYP_TAC (QCONV normalForms.CNF_CONV)) goal

(* ADD_BOOL_AXIOM_TAC *)
fun ADD_BOOL_AXIOM_TAC_w goal =
  if has_boolarg_goal goal 
  then ASSUME_TAC (CONJUNCT1 BOOL_EQ_DISTINCT) goal
  else ALL_TAC goal
fun ADD_BOOL_AXIOM_TAC goal = 
  wrap "tactic" "ADD_BOOL_AXIOM_TAC" "" ADD_BOOL_AXIOM_TAC_w goal

(* ADD_HIGHER_ORDER_TAC *)
fun add_higher_order goal = 
  let val appname = list_create_newname "App" (fst goal) in
    conv_hyp (QCONV (app_conv appname)) goal
  end      
  
fun add_higher_order_val goal thm =
  let val appname = list_create_newname "App" (fst goal) in
  let val eqthl = map (QCONV (app_conv appname)) (fst goal) in
  let val appl = erase_double_term (List.concat (map hyp eqthl)) in
  let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
  let val th0 = list_PROVE_HYP lemmal thm in
  let val th1 = remove_unused_extdefl appl th0 in
    thm_test th1 goal "add_higher_order_val"
  end end end end end end 
  
fun ADD_HIGHER_ORDER_TAC_w goal =
  if firstorder_goal goal
  then ALL_TAC goal
  else (flag_on hoflag;
        mk_tac1 add_higher_order add_higher_order_val goal)
fun ADD_HIGHER_ORDER_TAC goal = 
  wrap "tactic" "ADD_HIGHER_ORDER_TAC" "" ADD_HIGHER_ORDER_TAC_w goal 

(* ADD_FNUM_AXIOMS_TAC *)
local fun is_interesting (var,arity) = 
  let val (_,(imagety,_)) = strip_type_n (type_of var,arity) in
    imagety = ``:num`` andalso arity > 0
  end 
in 
  fun ADD_FNUM_AXIOMS_TAC_w goal =
    let val varal1 = all_vara_goal goal in
    let val varal2 = filter is_interesting varal1 in
    let val axioml = map fnum_axiom varal2 in
      list_ASSUME_TAC axioml goal
    end end end
end    
fun ADD_FNUM_AXIOMS_TAC goal = 
  wrap "tactic" "ADD_FNUM_AXIOMS_TAC" "" ADD_FNUM_AXIOMS_TAC_w goal 

(* BOOL_BV_TAC *)
fun BOOL_BV_TAC_w goal =
  CONV_HYP_TAC (bool_bv_conv THENC normalForms.CNF_CONV) goal
fun BOOL_BV_TAC goal = 
  wrap "tactic" "BOOL_BV_TAC" "" BOOL_BV_TAC_w goal 
           
fun BEAGLE_CLAUSE_SET_TAC goal =
  wrap "tactic" "BEAGLE_CLAUSE_SET_TAC" ""
  (
  ERASE_EXISTS_TAC THEN 
  FORALL_CONJUNCTS_TAC THEN
  STRIP_CONJ_ONLY_HYP_TAC THEN
  ERASE_FORALL_TAC THEN
  ADD_BOOL_AXIOM_TAC THEN
  ADD_HIGHER_ORDER_TAC THEN
  ADD_FNUM_AXIOMS_TAC THEN
  BOOL_BV_TAC
  )
  goal

end