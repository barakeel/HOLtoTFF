structure rule :> rule =
struct

(*
load "listtools"; open listtools;
load "tools"; open tools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
show_assums := true; 
*)

open HolKernel Abbrev boolLib normalForms 
     stringtools listtools tools mydatatype 
     extractvar extracttype

fun RULE_ERR function message =
    HOL_ERR{origin_structure = "rule",
	    origin_function = function,
            message = message}

fun forall_conjuncts_conv term = 
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
  let val th22 = strip_conj_hyp th21 in
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
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val term = ``((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val thm = ASSUME term;
show_assums := true;
f*)

(* term should be an extentional definition *)
(* i.e. forall x y z, f x y z = x + y + z *)
(* test
val term = ``!x y z. f x y z = x + y + z``;
*)

fun def_conv term =
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
  let val th21 = list_ap_thm th20 bvl in
  let val th22 = conv_concl (RAND_CONV (REDEPTH_CONV BETA_CONV)) th21 in
  let val th23 = GENL bvl th22 in
  let val th24 = DISCH (concl th14) th23 in
  (* together *)
    IMP_ANTISYM_RULE th15 th24
  end end end end end 
  end end end end end 
  end end end end end 
  
(* REMOVE UNUSED DEFINITION *)
fun remove_unused_def def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end

fun remove_unused_defl defl thm = repeatchange remove_unused_def defl thm


end