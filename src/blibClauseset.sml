structure blibClauseset :> blibClauseset =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype 
     blibSyntax blibBrule 
     blibExtractvar blibExtracttype 

(* forall_conjuncts_conv *)
fun forall_conjuncts_conv_w term = 
  let val (bvl,t) = strip_forall term in
  (* first part *)
  let val th10 = ASSUME term in
  let val th11 = SPECL bvl th10 in
  let val thl12 = CONJUNCTS th11 in
  let val thl13 = map (GENL bvl) thl12 in
  let val th14 = LIST_CONJ thl13 in
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th20 = ASSUME (concl th14) in
  let val th21 = ASSUME t in
  let val th22 = strip_conj_hyp_rule th21 in
  let val thl23 = CONJUNCTS th20 in
  let val thl24 = map (SPECL bvl) thl23 in
  let val th25 = list_PROVE_HYP thl24 th22 in
  let val th26 = GENL bvl th25 in 
  let val th27 = DISCH (concl th14) th26 in
  (* together *)
    IMP_ANTISYM_RULE th15 th27
  end end end end end 
  end end end end end 
  end end end end end
fun forall_conjuncts_conv term = 
  wrap "blibClauseset" "forall_conjuncts_conv" "" forall_conjuncts_conv_w term  
  
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val term = ``((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val thm = ASSUME term;
show_assums := true;
f*)

(* test
val term = ``!x y z. f x y z = x + y + z``;
*)
 
(************ APP REMOVAL ***********)
(* def_conv *)
fun def_conv_w term =
  let val (bvl,t) = strip_forall term in
  let val abs = list_mk_abs (bvl,rhs t) in
  let val term1 = list_mk_comb (abs,bvl) in
  let val eqth = (REDEPTH_CONV BETA_CONV) term1 in
  (* first part *)
  let val th10 = ASSUME term in
  let val th11 = SPECL bvl th10 in
  let val th12 = TRANS th11 (SYM eqth) in
  let val th13 = GENL bvl th12 in
  let val th14 = EXTL bvl th13 in
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th20 = ASSUME (concl th14) in
  let val th21 = list_AP_THM th20 bvl in
  let val th22 = conv_concl (RAND_CONV (REDEPTH_CONV BETA_CONV)) th21 in
  let val th23 = GENL bvl th22 in
  let val th24 = DISCH (concl th14) th23 in
  (* together *)
    IMP_ANTISYM_RULE th15 th24
  end end end end end 
  end end end end end 
  end end end end end 
fun def_conv term = 
  wrap "blibClauseset" "def_conv" "" def_conv_w term  

fun remove_unused_def_w def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end
fun remove_unused_def def thm =
  wrap "blibClauseset" "remove_unuse_def" "" 
    (remove_unused_def_w def) thm  


fun remove_unused_defl defl thm = repeatchange remove_unused_def defl thm

fun remove_unused_extdefl_w appl thm =  
  let val th0 = conv_hypl def_conv appl thm in
  let val th1 = remove_unused_defl (map (rhs o concl o def_conv) appl) th0 in
    th1
  end end
  
fun remove_unused_extdefl appl thm =
  wrap "blibClauseset" "remove_unuse_appl" "" 
    (remove_unused_extdefl_w appl) thm   
(* end app removal *)

(* term should start with !x:bool *)
fun bool_bv_conv_sub term =
  let val var = (hd o fst o strip_forall) term in
  if not (has_boolty var) then raise UNCHANGED
  else
    (* preparation *)  
  let val disj = SPEC var BOOL_CASES_AX in
  let val lemma = SPEC var (ASSUME term) in
  let val eqth1 = ASSUME (lhand (concl disj)) in
  let val eqth2 = ASSUME (rand (concl disj)) in
    (* first part *)
  let val th11 = ASSUME term in
  let val th12 = SPEC T th11 in
  let val th13 = SPEC F th11 in
  let val th14 = CONJ th12 th13 in
  let val th15 = DISCH term th14 in
    (* second part *)
  let val goalT = ([lhand(concl disj), concl th14],concl lemma) in
  let val (_,fnT) = SUBST_TAC [eqth1] goalT in  
  let val th20T = ASSUME (concl th14) in
  let val th21T = CONJUNCT1 th20T in
  let val th22T = fnT [th21T] in

  let val goalF = ([rand(concl disj), concl th14],concl lemma) in
  let val (_,fnF) = SUBST_TAC [eqth2] goalF in  
  let val th20F = ASSUME (concl th14) in
  let val th21F = CONJUNCT2 th20F in
  let val th22F = fnF [th21F] in
    (* disj cases *)
  let val th30 = DISJ_CASES disj th22T th22F in
  let val th31 = GEN var th30 in
  let val th32 = DISCH (concl th14) th31 in
  (* together *)
    IMP_ANTISYM_RULE th15 th32
  end end end end end 
  end end end end end
  end end end end end 
  end end end end end
  end end end
  
fun bool_bv_conv term =
  if not (is_forall term) 
  then raise UNCHANGED
  else 
    (QUANT_CONV bool_bv_conv THENC bool_bv_conv_sub) term
    
(* test 
val term = ``!x:bool y:num z:bool. x /\ (y = 0) /\ z``;     
*)


end