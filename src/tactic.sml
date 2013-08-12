structure tactic :> tactic =
struct

open HolKernel Abbrev boolLib
     stringtools listtools tools mydatatype 
     extractvar extracttype freshvar higherorder
     conv clausesettools printtools

(************ TOOLS ***************)
(* TAC BUILDER *)
exception MATCH

fun mk_tac1 goalbuilder valbuilder goal =
  let val goal_list = [goalbuilder goal] in
  let val validation = fn [thm] => valbuilder goal thm  
                       | _     => raise MATCH            
  in
     (goal_list,validation)
  end end

(* CONV_ONLY_HYP_TAC *)
fun conv_only_hyp_val conv goal thm =
  let val eqth = conv (only_hypg goal) in
  let val lemma = UNDISCH (fst (EQ_IMP_RULE eqth)) in
  let val th1 = PROVE_HYP lemma thm in
    thm_test th1 goal "conv_only_hyp"
  end end end

fun conv_only_hyp conv goal =
  let val eqth = conv (only_hypg goal) in
  let val term = rhs (concl eqth) in
    ([term],snd goal)
  end end 

fun CONV_ONLY_HYP_TAC conv goal = 
  mk_tac1 (conv_only_hyp conv) (conv_only_hyp_val conv) goal

(*********** PROBLEM_TO_GOAL_TAC ************)
  (* CONJ_ALL_HYP_TAC *)
fun conj_all_hyp goal = 
  ([list_mk_conj (fst goal)],snd goal)
  
fun conj_all_hyp_val goal thm =
  let val lemma = LIST_CONJ (map ASSUME (fst goal)) in
  let val th1 = PROVE_HYP lemma thm in
    thm_test th1 goal "conj_all_hyp_val"
  end end

fun CONJ_ALL_HYP_TAC goal = 
  if null (fst goal) then ALL_TAC goal 
  else mk_tac1 conj_all_hyp conj_all_hyp_val goal
  
  (* ASSUME_THML_TAC *)
fun thml_axiom thml = LIST_CONJ (map (GEN_ALL o DISCH_ALL) thml)

fun ASSUME_THML_TAC thml goal =
  (if null thml then ALL_TAC else ASSUME_TAC (thml_axiom thml)) goal

  (* *)
fun PROBLEM_TO_GOAL_TAC thml goal =
  (
  CONJ_ALL_HYP_TAC THEN
  CCONTR_TAC THEN
  CONJ_ALL_HYP_TAC THEN
  (ASSUME_THML_TAC thml) THEN
  CONJ_ALL_HYP_TAC
  )
  goal

(* BEAGLE_CONV_TAC *)   
fun beagle_conv term = 
  QCONV 
  (
  normalForms.CNF_CONV THENC 
  fun_conv THENC   
  bool_conv THENC 
  num_conv THENC
  normalForms.CNF_CONV
  )
  term

fun BEAGLE_CONV_TAC goal = CONV_ONLY_HYP_TAC beagle_conv goal

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
  mk_tac1 erase_exists erase_exists_val goal
 
  (* FORALL_CONJUNCTS_TAC *)
fun FORALL_CONJUNCTS_TAC goal = CONV_ONLY_HYP_TAC forall_conjuncts_conv goal

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
  mk_tac1 strip_conj_only_hyp strip_conj_only_hyp_val goal
  
  (* ERASE_FORALL_TAC *)
fun erase_forall goal =
  let val terml = map (rhs o concl o (QCONV normalForms.CNF_CONV)) (fst goal) in
    (terml,snd goal)
  end 
  
fun erase_forall_val goal thm =
  let val terml = map (rhs o concl o (QCONV normalForms.CNF_CONV)) (fst goal) in
  let val eqthl = map (QCONV normalForms.CNF_CONV) (fst goal) in  
  let val lemmal1 = map (fst o EQ_IMP_RULE) eqthl in
  let val lemmal2 = map UNDISCH lemmal1 in   
    list_PROVE_HYP lemmal2 thm
  end end end end
  
fun ERASE_FORALL_TAC goal =
  mk_tac1 erase_forall erase_forall_val goal
    
  (* ADD_BOOL_AXIOM_TAC *)
fun ADD_BOOL_AXIOM_TAC goal =
  if has_boolarg_goal goal 
  then ASSUME_TAC (CONJUNCT1 BOOL_EQ_DISTINCT) goal
  else ALL_TAC goal

  (* ADD_HIGHER_ORDER_TAC *)
fun add_higher_order goal = 
  let val appname = list_create_newname "App" (fst goal) in
  let val terml = erase_double_term
    (map (rhs o concl o (QCONV (app_conv appname))) (fst goal)) in
    (terml,snd goal)
  end end        
  
fun add_higher_order_val goal thm =
  let val appname = list_create_newname "app" (fst goal) in
  let val eqthl = map (QCONV (app_conv appname)) (fst goal) in
  let val appl = erase_double_term (List.concat (map hyp eqthl)) in
  let val lemmal1 = map (fst o EQ_IMP_RULE) eqthl in
  let val lemmal2 = map UNDISCH lemmal1 in
  let val th0 = list_PROVE_HYP lemmal2 thm in
  let val th1 = remove_unused_app appl th0 in
    thm_test th1 goal "add_higher_order_val"
  end end end end end 
  end end
  
fun ADD_HIGHER_ORDER_TAC goal =
  if firstorder_goal goal
  then ALL_TAC goal
  else (flag_on hoflag;
        mk_tac1 add_higher_order add_higher_order_val goal)
  (* *)
fun BEAGLE_CLAUSE_SET_TAC goal =
  (
  ERASE_EXISTS_TAC THEN 
  FORALL_CONJUNCTS_TAC THEN
  STRIP_CONJ_ONLY_HYP_TAC THEN
  ERASE_FORALL_TAC THEN
  ADD_BOOL_AXIOM_TAC THEN
  ADD_HIGHER_ORDER_TAC
  )
  goal

end