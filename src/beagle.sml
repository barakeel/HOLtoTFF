structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib HOLPP 
     listtools tools printtools
     freshvar namevar
     higherorder monomorph conv rule tactic
     printtff printresult

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}


val hoflag = ref (false,"higher_order");
val mflag = ref (false,"polymorph");
val boolflag = ref (false,"bool");

fun turn_on flag = flag := (true,snd (!flag))
fun turn_off flag = flag := (false,snd (!flag))
fun update_flag flag value = flag := (value, snd(!flag))

(* BEAGLE NF *)

(* PROBLEM_TO_GOAL_TAC *)
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

  (* MAIN *)
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

(* BEAGLE_CLAUSE_SET_TAC *)
 
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

(* STRIP_CONJ_GOAL_TAC *)
fun strip_conj_goal goal =  
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
    (terml,snd goal)
  end
  
fun strip_conj_goal_val goal thm =
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
  let val thml = CONJUNCTS (ASSUME (only_hypg goal)) in
    list_PROVE_HYP thml thm
  end end
      
fun STRIP_CONJ_GOAL_TAC goal =
  mk_tac1 strip_conj_goal strip_conj_goal_val goal
  
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
  then (turn_on boolflag; ASSUME_TAC (CONJUNCT1 BOOL_EQ_DISTINCT) goal)
  else ALL_TAC goal

(* ADD_HIGHER_ORDER_TAC *)
fun add_higher_order goal = 
  let val APPname = list_create_newname "APP" (fst goal) in
  let val terml = erase_double_term
    (map (rhs o concl o (QCONV (APP_conv APPname))) (fst goal)) in
    (terml,snd goal)
  end end        
  
fun add_higher_order_val goal thm =
  let val APPname = list_create_newname "APP" (fst goal) in
  let val eqthl = map (QCONV (APP_conv APPname)) (fst goal) in
  let val APPl = erase_double_term (List.concat (map hyp eqthl)) in
  let val lemmal1 = map (fst o EQ_IMP_RULE) eqthl in
  let val lemmal2 = map UNDISCH lemmal1 in
  let val th0 = list_PROVE_HYP lemmal2 thm in
  let val th1 = remove_unused_APP APPl th0 in
    thm_test th1 goal "add_higher_order_val"
  end end end end end 
  end end
  
fun ADD_HIGHER_ORDER_TAC goal =
  if firstorder_goal goal
  then ALL_TAC goal
  else (turn_on hoflag;
        mk_tac1 add_higher_order add_higher_order_val goal)
(* beagle_clauseset main *)
fun BEAGLE_CLAUSE_SET_TAC goal =
  (
  ERASE_EXISTS_TAC THEN 
  FORALL_CONJUNCTS_TAC THEN
  STRIP_CONJ_GOAL_TAC THEN
  ERASE_FORALL_TAC THEN
  ADD_BOOL_AXIOM_TAC THEN
  ADD_HIGHER_ORDER_TAC
  )
  goal
  
(* test 
val term = ``x = 0 /\ y = 0``;
*)
  
(* BEAGLE_NF *)               
fun BEAGLE_NF_TAC thml goal =
  (
  PROBLEM_TO_GOAL_TAC thml THEN
  BEAGLE_CONV_TAC THEN
  BEAGLE_CLAUSE_SET_TAC
  )
  goal 

fun beagle_nf_info filename thml goal =
  let val goal1 = hd (fst (PROBLEM_TO_GOAL_TAC thml goal)) in
    output_beagle_conv filename goal1
  end
  handle _ => ()
  
(* test
show_assums:= true; 
val finalgoal = beagle_nf filename thml goal;
val thm = mk_thm finalgoal;
*)
  
(* BEAGLE INTERACTION *)
(* status *)
val SZSstatus = ref "undefined"

fun update_SZSstatus filename = 
  let val SZSstatuspath = mk_SZSstatuspath filename in
  let val file = TextIO.openIn SZSstatuspath in 
  let val str = TextIO.inputAll file in
    (
    SZSstatus := str;
    TextIO.closeIn file
    )  
  end end end   

fun beagle_interact filename finalgoal =
  (
  (* print the problem *)
  output_tffgoal (mk_tffpath filename) finalgoal false; 
  output_tffgoal (mk_tffsavepath filename) finalgoal true;
  output_tffgoalpath (mk_tffpath filename); 
  (* call beagle on tffpath *)
  OS.Process.system 
          ("cd " ^ directory ^ ";" ^
           "sh " ^ directory ^ "callbeagle.sh");
  (* *)
  update_SZSstatus filename
  )

(* test 
update_SZSstatus "problem6";
(!SZSstatus) = "Unsatisfiable";
*)
fun output_proof_err filename f m =
  let val file = TextIO.openAppend (mk_resultpath filename) in 
    (
    TextIO.output (file,"Err: " ^ f ^ " message: " ^ m);
    TextIO.closeOut file
    )  
  end
  
fun goal_to_string goal = thm_to_string (mk_thm goal)
    
  
(* BEAGLE_TAC *)
fun beagle_tac_aux filename thml goal = 
  (
  app turn_off [mflag,hoflag,boolflag];
  update_flag mflag (exists is_polymorph_thm thml);
  
  let val (finalgoal_list,validation) = BEAGLE_NF_TAC thml goal 
    handle  HOL_ERR{origin_structure = s,
	                  origin_function = f,
                    message = m}
           => (output_proof_err filename f m; raise BEAGLE_ERR "" "") 
       | _ => (output_proof_err filename "" "sml"; raise BEAGLE_ERR "" "") 
  in
  let val finalgoal = hd (finalgoal_list) in
    beagle_interact filename finalgoal (* update the status *)
      handle _ => raise output_error (mk_resultpath filename) 
                          ("Printing or interaction error : " ^ 
                          (goal_to_string finalgoal) ^ "\n")
  end end; 
  output_result filename thml goal (!SZSstatus) [!mflag,!hoflag,!boolflag];
  beagle_nf_info filename thml goal;
  ([],fn x => (mk_thm goal))
  )
  handle _ => ([],fn x => (mk_thm goal))

fun beagle_tac_poly filename thml goal = 
  if exists is_polymorph_thm thml 
  then
    (beagle_tac_aux filename thml goal;
     beagle_tac_aux filename (monomorph_rule thml goal) goal)
  else 
    beagle_tac_aux filename thml goal

fun BEAGLE_TAC thml goal = 
  let val filename = "beagletacresult/beagletac" in 
    beagle_tac_aux filename thml goal
  end
  

end  