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
fun thml_lemma thml = LIST_CONJ (map DISCH_ALL thml)

fun thml_to_hypt thml = concl (thml_lemma thml)

fun goal_to_hypt goal =
  if null (fst goal) 
  then mk_neg (snd goal)
  else mk_conj (list_mk_conj (fst goal),mk_neg (snd goal))

fun problem_to_hypt thml goal =
  if null thml 
  then goal_to_hypt goal
  else mk_conj (thml_to_hypt thml,goal_to_hypt goal)

fun problem_goal thml goal = ([problem_to_hypt thml goal],F)


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
    (* at this point there is no more conj thml *)
    if null (fst goal) then CCONTR (snd goal) th1
    else 
      let val th4 = unconj_hyp (hd (hyp th1)) th1 in     
      let val th5 = CCONTR (snd goal) th4 in         
      let val th6 = list_unconj_hyp goal th5 in
        th6
      end end end
  end end 
(* end proof *)

(* beagle_convert *)   

fun output_beagle_conv filename term =
  let val (file,pps) = pp_open (mk_convpath filename) true in
  let val eqth1 = QCONV normalForms.CNF_CONV term in 
  let val eqth2 = QCONV fun_conv term1 in 
  let val eqth3 = QCONV bool_conv term2 in 
  let val eqth4 = QCONV num_conv term3 in 
  let val eqth5 = QCONV normalForms.CNF_CONV term4 in 
    (  
    begin_block pps CONSISTENT 0;
    pp_conv pps "CNF1" eqth1;
    pp_conv pps "FUN " eqth2;
    pp_conv pps "BOOL" eqth3;
    pp_conv pps "NUM " eqth4;
    pp_conv pps "CNF2" eqth5;
    end_block pps;
    )
  end end end end end end

fun beagle_conv term = 
    let val eqth1 = QCONV normalForms.CNF_CONV term in 
    let val eqth2 = QCONV fun_conv term1 in 
    let val eqth3 = QCONV bool_conv term2 in 
    let val eqth4 = QCONV num_conv term3 in 
    let val eqth5 = QCONV normalForms.CNF_CONV term4 in 
      list_TRANS [eqth1,eqth2,eqth3,eqth4,eqth5]
    end end end end end

fun beagle_convert_val goal thm =
  let val eqth = beagle_conv (only_hypg goal) in
  let val lemma = UNDISCH (fst (EQ_IMP_RULE eqth)) in
    PROVE_HYP lemma thm
  end end

fun beagle_convert goal =
  let val eqth = beagle_conv (only_hypg goal) in
  let val term = rhs (concl eqth) in
    ([term],snd goal)
  end end 

(* beagle clause set *)
 
(* erase exists *)
fun erase_exists_val goal thm =
  (* term construction *)
  let val (hypl,ccl) = goal in
  let val (bvl,t) = strip_exists term in
  (* proof *) 
  let val th1 = DISCH (alone_hyp thm) thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL bvl th2 in
  let val th4 = conv_concl (QCONV strip_forall_not_conv) th3 in
  let val th5 = NOT_ELIM th4 in
  let val th6 = UNDISCH th5 in
    if mk_goal th6 = goal then th6 
    else raise BEAGLE_ERR "erase_exists_val" "" 
  end end end end end 
  end end end
 
fun erase_exists goal =
  let val (bvl,t) = strip_exists (alone_hypg goal) in 
    (t,snd goal)
  end 
  
(* forall conjuncts *) (* typical of conv *) 
fun forall_conjuncts_val goal thm =
  let val eqth = forall_conjuncts_conv (alone_hypg goal) in
  let val (lemma1,_) = IMP_ANTISYM_RULE eqth in
  let val lemma2 = UNDISCH lemma1 in   
    PROVE_HYP lemma2 thm
  end end end
  
fun forall_conjuncts goal =
  let val eqth = forall_conjuncts_conv (alone_hypg goal) in
    (rhs (concl eqth)),snd goal)
  end
(* erase unused quantifier *)


(* idea: should erase aconvertible terms in fst goal 
to make it looks like a thm *)

(* strip_conj_hyp *)
fun strip_conj_hyp_val goal thm =
  let val terml = erase_double_aconv (strip_conj (alone_hypg goal)) in
  let val thml = CONJUNCTS (ASSUME (alone_hypg goal)) in
    list_PROVE_HYP thml thm
  end end
 
fun strip_conj_hyp goal =  
  let val terml = erase_double_aconv (strip_conj (alone_hypg goal)) in
    (terml,snd goal)
  end
  
(* erase forall *)
fun erase_forall_val goal thm =
  let val terml = map (rhs o concl o (QCONV normalForms.CNF_CONV)) (fst goal) in
  let val eqthl = map (QCONV normalForms.CNF_CONV) (fst goal) in  
  let val lemmal1 = map (fst IMP_ANTISYM_RULE) eqthl in
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
fun remove_unused_app thm =  
  let val th0 = conv_hypl def_conv (hyp thm) thm in
  let val th1 = remove_unused_defl (hyp th0) th0 in
    th1
  end end
 

(* test is first_order_goal *)
fun add_higher_order_val goal thm =
  let val appname = list_create_newname "app" (fst goal) in
  let val eqthl = map (QCONV (app_conv appname)) (fst goal) in
  let val lemmal1 = map (fst IMP_ANTISYM_RULE) eqthl in
    (* remove unused app too complex? *) 
  let val lemmal2 = map remove_unused_app lemmal1 in
  let val lemmal3 = map UNDISCH lemmal1 in   
  let val th0 = list_PROVE_HYP lemmal3 thm in
    if mk_goal th0 = goal then th0
    else raise BEAGLE_ERR "higher_order_val" "" 
  end end end end end
  
  
fun add_higher_order goal = 
  let val appname = list_create_newname "app" (fst goal) in
  let val terml = erase_double_aconv
    map (rhs o concl o (QCONV (app_conv appname)) (fst goal) in
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
  let val goal5 = add_axioms goal4 in
  let val goal6 = add_higher_order goal5 in
  let val th1 = add_higher_order_val goal5 thm in
  let val th2 = add_axioms_val goal4 th1 in
  let val th3 = erase_forall_val goal3 th2 in
  let val th4 = strip_conj_hyp_val goal2 th3 in
  let val th5 = forall_conjuncts_val goal1 th4 in
  let val th6 = erase_exists_val goal th5 in
    th6
  end end end end end end
  end end end end end end  
  
fun beagle_clauseset goal =
  let val goal1 = erase_exists goal in
  let val goal2 = forall_conjuncts goal1 in
  let val goal3 = strip_conj_hyp goal2 in
  let val goal4 = erase_forall goal3 in
  let val goal5 = add_axioms goal4 in
  let val goal6 = add_higher_order goal5 in
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
  let val th2 = beagle_convert_val goal1 thm in
  let val th3 = problem_to_goal_val thml goal thm in
    th3
  end end end end end end

fun beagle_nf filename thml goal =
 (* (* monomorphisation *)
  let val term2 = if mflag then monomorph term1 else term1
  in *)
  (* problem to term *)
  let val goal1 = problem_to_goal thml goal in 
  (* conversion cnf + bool + num + abs *)
  let val goal2 = beagle_convert goal1 in
  (* clause set + app *)
  let val goal3 = beagle_clauseset goal2 in
    (output_beagle_conv filename (alone_hypg goal1);
     goal3)
  end end end (* end *)

(* test
show_assums:= true; 
val beagle_nf filename thml goal;
val thm = mk_thm finalgoal;
val term = term3;
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

fun output_finalthm thm =
  (show_assums := true;
   output_info (mk_proofpath filename) ((thm_to_string thm) ^ "\n");
   show_assums := false)

(* BEAGLE_TAC *)
fun beagle_tac_aux filename thml goal =
  (* handle polymorphism *)
  (* should instantiate *)
  let val result = ([],fn x => (mk_thm goal)) in
  let val mflag = is_polymorph_pb thml goal in
    (
    let val finalgoal = beagle_nf filename thml goal 
      handle _ => raise output_error (mk_resultpath filename) "nf"
    in
    let val thm = beagle_nf_val thml goal (mk_thm finalgoal) 
      handle _ => (output_info (mk_resultpath filename) "nf_val"; ASSUME T)
    in
      (
      output_finalthm thm;
      beagle_interact filename finalgoal (* update the status *)
        handle _ => raise output_error (mk_resultpath filename) "interact"
      )
    end end
    ; 
    output_result (mk_resultpath filename) goal (!SZSstatus) mflag
    ;
    case (!SZSstatus) of
        "Unsatisfiable" => result
      | _ => result
    )
    handle _ => result
  end end 


fun BEAGLE_TAC thml goal = 
  let val filename = "beagletacresult/beagletac" in 
    beagle_tac_aux filename thml goal
  end
  
  
end  