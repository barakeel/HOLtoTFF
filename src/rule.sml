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

(* NEGATE conclt *)
(* need to memorise the conclt somewhere to be able to replay the proof back *)
fun negate_concl thm =
  let val t0 = concl thm in
  let val t1 = mk_neg t0 in
  let val th0 = ASSUME t1 in
  let val th1 = NOT_ELIM th0 in
    MP th1 thm
  end end end end   
 
(* thm should have a conclt equal to false and conclt be a negation *)
fun negate_concl_rev conclt thm = CCONTR conclt thm

(* test 
show_assums :=  true ;
val thm = ASSUME ``A:bool``;
negate_concl thm;
*)

(* BOOL AXIOM *)
fun add_bool_axioms thm = 
  if has_boolarg_thm thm
  then ADD_ASSUM (concl BOOL_EQ_DISTINCT) thm
  else thm

fun remove_bool_axioms thm =
  list_prove_hyp [BOOL_EQ_DISTINCT] thm

(* test
show_assums := true ;
val thm = ASSUME ``A:bool``;
val thm = ASSUME ``P (A:bool) :bool``;
add_bool_axioms thm;
find_unpredicatel (concl thm);
has_boolty ``A:bool``;
has_boolarg_thm thm;
remove_bool_axioms it;
*)
(* EXISTS RULE *)
(* thm should have conclt set to false *)
(* specify with their own names *)
(* hypt should be in cnf *)

(* hyp should start with exists and concl thm should be F*)
fun remove_exists hypt thm =
  if is_exists hypt 
  then
    let val varl = fst (strip_exists hypt) in
    let val th1 = DISCH hypt thm in
    let val th2 = NOT_INTRO th1 in
    let val th3 = conv_concl not_exists_list_conv th2 in
    let val th4 = SPECL varl th3 in
    let val th5 = NOT_ELIM th4 in
    let val th6 = UNDISCH th5 in
      th6
    end end end end end 
    end end
  else thm
  
(* should remember which varl were existentially quantified 
   to be able to go back *)
fun remove_exists_thm thm =
  let val hyptl = hyp thm in
    repeatchange remove_exists hyptl thm 
  end

(* test
val hypt = ``~(?x y z. x + y + z = 0)``; 
val thm = mk_thm ([hypt],F);
*) 

fun add_exists (hypt,varl) thm =
  let val th1 = DISCH hypt thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL varl th2 in
  let val th4 = FORALL_NOT_CONV (concl th3) in
  let val th5 = EQ_MP th4 th3 in
  let val th6 = NOT_ELIM th5 in
  let val th7 = UNDISCH th6 in
    th7
  end end end end end 
  end end

fun add_existsl l thm = repeatchange add_exists l thm
  

(* test
val thm = mk_thm ([hypt],F);
val hypt = ``x + y = 0``;
show_assums := true;
val varl = map fst (filter_fval (extract_var hypt));
*)

(* thm should be in cnf form with existential quantifiers removed *)
fun stripforall_conjlist thm = 
  let val term = concl thm in
  let val (bvl,t) = strip_forall term in
  let val th0 = SPECL bvl thm in
  let val thl0 = CONJUNCTS th0 in
  let val thl1 = map (GENL bvl) thl0 in
  let val thl2 = map (conv_concl normalForms.CNF_CONV) thl1 in
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val thm = ASSUME term;
show_assums := true;
*)

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