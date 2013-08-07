structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib HOLPP 
     listtools tools printtools
     freshvar namevar
     higherorder monomorph conv rule 
     printtff printresult

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}
 
(* Path (absolute) *)
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
fun mk_holpath filename = directory ^ filename ^ "_hol"  
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_SZSstatuspath filename = directory ^ filename ^ "_tff_SZSstatus"
fun mk_resultpath filename = directory ^ filename ^ "_result"
fun mk_convpath filename = directory ^ filename ^ "_conv"
fun mk_addresspath () = directory ^ "filepath.txt"
fun mk_tffsavepath filename = directory ^ filename ^ "_tffsave"
fun mk_proofpath filename = directory ^ filename ^ "_proof"

(* BEAGLE NF *)

(* problem to a term *)
fun thml_lemma thml = LIST_CONJ (map (GEN_ALL o DISCH_ALL) thml)

fun thml_to_hypt thml = concl (thml_lemma thml)

fun goal_to_hypt goal =
  if null (fst goal) 
  then mk_neg (snd goal)
  else mk_conj (list_mk_conj (fst goal),mk_neg (snd goal))

fun problem_to_hypt thml goal =
  if null thml 
  then goal_to_hypt goal
  else mk_conj (thml_to_hypt thml,goal_to_hypt goal)

fun problem_to_goal thml goal = ([problem_to_hypt thml goal],F)

fun list_unconj_hyp goal thm =
  let val lemma = LIST_CONJ (map ASSUME (fst goal)) in
    PROVE_HYP lemma thm
  end

 
(* thm : term |- F *)
(* goal : hypl |? concl *)  
fun problem_to_goal_val thml goal thm =
  let val hypt = problem_to_hypt thml goal in
  let val th1 = 
    if null thml then thm 
    else 
      let val lemma1 = thml_lemma thml in
      let val th2 = unconj_hyp hypt thm in
      let val th3 = PROVE_HYP lemma1 th2 in
        ADD_ASSUM (goal_to_hypt goal) th2 (* if it was in the thml *)
      end end end
  in
  let val th4 =
    if null (fst goal) then CCONTR (snd goal) th1
    else 
      let val th5 = unconj_hyp (only_hyp th1) th1 in     
      let val th6 = CCONTR (snd goal) th5 in         
      let val th7 = list_unconj_hyp goal th6 in
        th6
      end end end
  in 
    if goal_eq (mk_goal th4) goal then th4 
    else raise BEAGLE_ERR "problem_to_goal" ""
  end end end
(* end proof *)


(* beagle_convert *)   

fun output_beagle_conv filename goal =
  let val file = TextIO.openAppend filename in
  let val eqth1 = QCONV normalForms.CNF_CONV (only_hypg goal) in 
  let val eqth2 = QCONV fun_conv  (rhs (concl eqth1)) in 
  let val eqth3 = QCONV bool_conv (rhs (concl eqth2)) in 
  let val eqth4 = QCONV num_conv  (rhs (concl eqth3)) in 
  let val eqth5 = QCONV normalForms.CNF_CONV (rhs (concl eqth4)) in 
    (  
    outstream_eqth file "CNF1" eqth1;
    outstream_eqth file "FUN " eqth2;
    outstream_eqth file "BOOL" eqth3;
    outstream_eqth file "NUM " eqth4;
    outstream_eqth file "CNF2" eqth5;
    TextIO.output(file,"\n");
    TextIO.closeOut file 
    )
  end end end end end end

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

fun beagle_convert_val goal thm =
  let val eqth = beagle_conv (only_hypg goal) in
  let val lemma = UNDISCH (fst (EQ_IMP_RULE eqth)) in
  let val th1 = PROVE_HYP lemma thm in
    if goal_eq (mk_goal th1) goal then th1 
    else raise BEAGLE_ERR "convert_val" ""
  end end end

fun beagle_convert goal =
  let val eqth = beagle_conv (only_hypg goal) in
  let val term = rhs (concl eqth) in
    ([term],snd goal)
  end end 

(* beagle clause set *)
 
(* erase exists *)
fun erase_exists_val goal thm =
  (* term construction *)
  let val (bvl,t) = strip_exists (only_hypg goal) in
  (* proof *) 
  let val th1 = DISCH (only_hyp thm) thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL bvl th2 in
  let val th4 = conv_concl (QCONV strip_forall_not_conv) th3 in
  let val th5 = NOT_ELIM th4 in
  let val th6 = UNDISCH th5 in
    if goal_eq (mk_goal th6) goal then th6 
    else raise BEAGLE_ERR "erase_exists_val" "" 
  end end end end end 
  end end
 
fun erase_exists goal =
  let val (bvl,t) = strip_exists (only_hypg goal) in 
    ([t],snd goal)
  end 
 
(* forall conjuncts *)
fun forall_conjuncts_val goal thm =
  let val eqth = forall_conjuncts_conv (only_hypg goal) in
  let val lemma = UNDISCH (fst (EQ_IMP_RULE eqth)) in
    PROVE_HYP lemma thm
  end end 
  
fun forall_conjuncts goal =
  let val eqth = forall_conjuncts_conv (only_hypg goal) in
    ([rhs (concl eqth)],snd goal)
  end
(* erase unused quantifier *)

(* idea: should erase aconvertible terms in fst goal 
to make it looks like a thm *)

(* strip_conj_hyp *)
fun strip_conj_hyp_val goal thm =
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
  let val thml = CONJUNCTS (ASSUME (only_hypg goal)) in
    list_PROVE_HYP thml thm
  end end
 
fun strip_conj_hyp goal =  
  let val terml = erase_double_term (strip_conj (only_hypg goal)) in
    (terml,snd goal)
  end
    
(* erase forall *)
fun erase_forall_val goal thm =
  let val terml = map (rhs o concl o (QCONV normalForms.CNF_CONV)) (fst goal) in
  let val eqthl = map (QCONV normalForms.CNF_CONV) (fst goal) in  
  let val lemmal1 = map (fst o EQ_IMP_RULE) eqthl in
  let val lemmal2 = map UNDISCH lemmal1 in   
    list_PROVE_HYP lemmal2 thm
  end end end end
  
fun erase_forall goal =
  let val terml = map (rhs o concl o (QCONV normalForms.CNF_CONV)) (fst goal) in
    (terml,snd goal)
  end 
  

(* add_axioms *)
fun add_axioms_val goal thm =
  list_PROVE_HYP [CONJUNCT1 BOOL_EQ_DISTINCT] thm 

fun add_axioms goal =  
  let val term = concl (CONJUNCT1 BOOL_EQ_DISTINCT) in
    (term :: fst goal,snd goal)
  end
  
(* *)  

(* higher order could be optimized *)
fun remove_unused_app appl thm =  
  let val th0 = conv_hypl def_conv appl thm in
  let val th1 = remove_unused_defl (map (rhs o concl o def_conv) appl) th0 in
    th1
  end end


fun add_higher_order_val goal thm =
  let val appname = list_create_newname "app" (fst goal) in
  let val eqthl = map (QCONV (app_conv appname)) (fst goal) in
  let val appl = erase_double_term (List.concat (map hyp eqthl)) in
  let val lemmal1 = map (fst o EQ_IMP_RULE) eqthl in
  let val lemmal2 = map UNDISCH lemmal1 in
  let val th0 = list_PROVE_HYP lemmal2 thm in
  let val th1 = remove_unused_app appl th0 in
    if goal_eq (mk_goal th1) goal then th1
    else raise BEAGLE_ERR "add_higher_order_val" ""
  end end end end end 
  end end
  
fun add_higher_order goal = 
  let val appname = list_create_newname "app" (fst goal) in
  let val terml = erase_double_term
    (map (rhs o concl o (QCONV (app_conv appname))) (fst goal)) in
    (terml,snd goal)
  end end        

(* idea: should erase aconvertible terms in fst goal 
         to make it looks like a thm *) 
  
(* beagle_clauseset main *)
fun beagle_clauseset_val goal thm =
  let val goal1 = erase_exists goal in
  let val goal2 = forall_conjuncts goal1 in
  let val goal3 = strip_conj_hyp goal2 in
  let val goal4 = erase_forall goal3 in
  let val bool_flag = has_boolarg_goal goal4 in
  let val goal5 = if bool_flag then add_axioms goal4 else goal4 in
  let val fo_flag = firstorder_goal goal5 in
  let val goal6 = if fo_flag then goal5 else add_higher_order goal5 in
  let val th1 = if fo_flag then thm else add_higher_order_val goal5 thm in
  let val th2 = if bool_flag then add_axioms_val goal4 th1 else th1 in
  let val th3 = erase_forall_val goal3 th2 in
  let val th4 = strip_conj_hyp_val goal2 th3 in
  let val th5 = forall_conjuncts_val goal1 th4 in
  let val th6 = erase_exists_val goal th5 in
    th6
  end end end end end 
  end end end end end 
  end end end end
  
fun beagle_clauseset goal =
  let val goal1 = erase_exists goal in
  let val goal2 = forall_conjuncts goal1 in
  let val goal3 = strip_conj_hyp goal2 in
  let val goal4 = erase_forall goal3 in
  let val goal5 = if has_boolarg_goal goal4 
                  then add_axioms goal4
                  else goal4
  in
  let val goal6 = if firstorder_goal goal 
                  then goal5 
                  else add_higher_order goal5 
  in
    goal6
  end end end end end end
    
(* test 
val term = ``x = 0 /\ y = 0``;
*)

  
(* BEAGLE_NF *)               
fun beagle_nf_val thml goal thm =
  let val goal1 = problem_to_goal thml goal in 
  let val goal2 = beagle_convert goal1 in
  let val goal3 = beagle_clauseset goal2 in
  let val th1 = beagle_clauseset_val goal2 thm in
  let val th2 = beagle_convert_val goal1 th1 in
  let val th3 = problem_to_goal_val thml goal th2 in
    th3
  end end end end end end
  
  (* to do monomorphisation *)
fun beagle_nf filename thml goal =
  let val goal1 = problem_to_goal thml goal in 
  let val goal2 = beagle_convert goal1 in
  let val goal3 = beagle_clauseset goal2 in
    (output_beagle_conv (mk_convpath filename) goal1;
     goal3)
  end end end (* end *)

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
  (* path *)
  let val tffpath = mk_tffpath filename in
  let val tffsavepath = mk_tffsavepath filename in
  let val addresspath = mk_addresspath () in
    (* print the problem *)
    (
    output_tffgoal tffpath finalgoal false; 
    output_tffgoal tffsavepath finalgoal true;
    output_tffgoalpath addresspath tffpath; 
    (* call beagle on tffpath*)
    OS.Process.system 
          ("cd " ^ directory ^ ";" ^
           "sh " ^ directory ^ "callbeagle.sh");
    (* get the status of the thm into ref SZSstatus*)
    update_SZSstatus filename
    )
  end end end

(* test 
update_SZSstatus "problem6";
(!SZSstatus) = "Unsatisfiable";
*)

fun output_finalthm filename thm =
  (show_assums := true;
   output_info (mk_proofpath filename) ((thm_to_string thm) ^ "\n");
   show_assums := false)

(* BEAGLE_TAC *)
fun beagle_tac_aux filename thml goal = 
  let val result = ([],fn x => (mk_thm goal)) in
  let val mflag = exists is_polymorph_thm thml in
    (
    let val finalgoal = 
      beagle_nf filename thml goal
      handle _ => raise output_error (mk_resultpath filename) "(nf)"
    in
    let val thm = 
      beagle_nf_val thml goal (mk_thm finalgoal)
      handle _ => ASSUME T
    in
      (
      output_finalthm filename thm;
      beagle_interact filename finalgoal (* update the status *)
        handle _ => raise output_error (mk_resultpath filename) "(interact)"
      )
    end end
    ; 
    output_result (mk_resultpath filename) thml goal (!SZSstatus) mflag
    ;
    case (!SZSstatus) of
        "Unsatisfiable" => result
      | _ => result
    )
    handle _ => result
  end end 

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