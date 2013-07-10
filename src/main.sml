structure main :> main =
struct
(* 
load "normalize"; open normalize; 
load "printtff"; open printtff;
load "nametype"; open nametype;
load "extractvar"; open extractvar;
load "tools"; open tools;
load "listtools"; open listtools;
open Drule;
*)


open HolKernel 
     normalize printtff
     extractvar
     tools 

fun MAIN_ERR function message =
    HOL_ERR{origin_structure = "main",
	    origin_function = function,
            message = message}
 
(* Monomorphisation *)



(* Negate concl *)
fun negate_concl thm =
  let val t0 = concl thm in
  let val t1 = mk_neg t0 in
  let val th0 = ASSUME t1 in
  let val th1 = NOT_ELIM th0 in
    MP th1 thm
  end end end end   
 
(* input should have conclusion equal to false and goal be a negation *)
fun negate_concl_rev goal thm = CCONTR goal thm
(* need to memorise the goal somewhere to be able to replay the proof back *)
  
(* test 
show_assums :=  true ;
val thm = ASSUME ``A:bool``;
negate_concl thm;
*)

(* REWRITING and memorising dictionnaries *)
(* each term should be rewritten on its own ? *)
(* for now I just make a big conjunctions and rewrite it *)
(* for now thm should end with false *)
fun convert term = 
  (QCONV
  (
  beta_conv THENC
  eta_conv THENC
  normalForms.CNF_CONV THENC
  bool_conv THENC (* add new constants *)
  fun_conv THENC  (* add new constants *)
  app_conv THENC (*  add def should be remembered *)
  num_conv THENC (* add => *)
  normalForms.CNF_CONV THENC
  predicate_conv   (* required every variables to have a different name 
                      and every bound variables to be used 
                      (cnf_conv provide that) 
                      add def should be remembered *)
  ))
  term

(* try to get rid of cnf conv because I don't know what it do to variable name *)  
(* don't forget to make list of all this variables to remember them *)

val beagleproblemlocation =
  "/home/thibault/Desktop/Scalaproject/beagleproject/problem.p"
val testlocation = 
  "/home/thibault/Desktop/SMLproject/HOLtoTFF/output.txt"

fun prove_hyp_list thml thm =
  case thml of
    [] => thm
  | th :: m => prove_hyp_list m (PROVE_HYP th thm)  

fun list_conj_hyp thm =
  let val hypl = hyp thm in
  let val t1 = list_mk_conj hypl in
  let val thl = CONJ_LIST (length hypl) (ASSUME t1) in
  let val th2 = prove_hyp_list thl thm in
    th2
  end end end end  

(* Bool axiom *)
fun has_boolarg term = not (null (filter has_boolty (find_unpredicatel term)))

fun has_boolarg_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    exists has_boolarg l
  end  

fun all_var term = map fst (map fst (extract_var term))

fun all_var_thm thm =
  let val l = (hyp thm) @ [concl thm] in
    List.concat (map all_var l)
  end  
  
fun add_bool_axioms thm = 
  if has_boolarg_thm thm
  then
    let val var = mk_var ("b",``:bool``) in
    let val newvar = create_newvar var (all_var_thm thm) in
    let val eqth1 = RAND_CONV (ALPHA_CONV newvar) (concl BOOL_CASES_AX) in
    let val th1 = EQ_MP eqth1 BOOL_CASES_AX in   
    let val th2 = BOOL_EQ_DISTINCT in
    let val th3 = ADD_ASSUM (concl th1) thm in  
    let val th4 = ADD_ASSUM (concl th2) th3 in
      th4
    end end end end end end end
  else thm

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
fun remove_bool_axioms thm =
  PROVE_HYP BOOL_EQ_DISTINCT (PROVE_HYP BOOL_CASES_AX thm)
  
(* SKOLEM REWRITE *)
(* thm should have conclusion set to false *)
(* normally it's not bad to specify with their own names 
   since they do not appear free in hypothesis *)
(* term should have an unique existential quantifier at the start *)

fun remove_exists varl hypterm thm =
  let val th1 = DISCH hypterm thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL varl th2 in
  let val th4 = FORALL_NOT_CONV (concl th3) in
  let val th5 = EQ_MP th4 th3 in
  let val th6 = NOT_ELIM th5 in
  let val th7 = UNDISCH th6 in
    th7
  end end end end end 
  end end

fun remove_exists_all hypterm thm =
  let val (varl,t) = strip_exists hypterm in
    remove_exists varl hypterm thm
  end
(* should remember which varl were existentially quantified 
   to be able to go back *)
fun remove_exists_thm thm =
  let val hypl = hyp thm in
    repeatchange remove_exists_all hypl thm 
  end
    
fun add_exists varl hypterm thm =
  let val th1 = DISCH hypterm thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = NOT_EXISTS_CONV (concl th2) in
  let val th4 = EQ_MP th3 th2 in
  let val th5 = SPECL varl th4 in
  let val th6 = NOT_ELIM th5 in
  let val th7 = UNDISCH th6 in
    th7
  end end end end end 
  end end

fun add_exists_thm varll thm = repeatchange add_exists varll thm
(* test
val var = mk_var ("x",``:num``);
val var = mk_var ("y",``:num``);
val hypterm = ``?x y. x + y = 0``;
val thm = mk_thm ([hypterm],F);
val hypterm = ``x = 0``;
show_assums := true;
val varl = [var];
*)
(* END SKOLEM REWRITE *)

(* the furthest I can go is a clause set with only forall quantifier *)  


  

(* should output a theorem but printtff should be rewritten *)
(* MAIN *)
fun main thm = 
   let val th1 = negate_concl thm in
   let val th2 = list_conj_hyp th1 in
   (* conversion *)
   let val term = hd (hyp th2) in
   let val th3 = rewrite_conv_hyp convert term
   (* remove all existential quantifiers from all hypterms*)
   let val th4 = remove_exists_thm in 
   (* add bool_axiom *)  
   let val th5 = add_bool_axioms th4 in  
   (* print it *)  
     output_tff testlocation th5
   end end end end end end end

(* first assume all the hypothesis *)
(* at least one hypothesis anyway *)


fun remove_unused_def def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end

fun remove_unused_defl defl thm = repeatchange remove_unused_def defl thm


(* app def *)

fun ap_thml thm terml =
  case terml of
    [] => thm 
  | t :: m => ap_thml (AP_THM thm t) m 

fun define_conv appdef =
  let val (bvl,t) = strip_forall appdef in
  (* one way *)
  let val th11 = ASSUME appdef in
  let val th12 = SPECL bvl th11 in
  let val th13 = repeatchange ABS (rev bvl) th12 in
  let val th14 = rewrite_conv (LAND_CONV eta_conv) th13 in 
  let val th15 = DISCH appdef th14 in
  (* otherway *)
  let val th21 = ASSUME (concl th14) in
  let val th22 = ap_thml th21 bvl in
  let val th23 = rewrite_conv beta_conv th22 in
  let val th24 = GENL bvl th23 in
  let val th25 = DISCH (concl th14) th24 in
  (* together *)
    IMP_ANTISYM_RULE th15 th25
  end end end end end 
  end end end end end
  end




(* test
val appdef = ``!x y. app x y = x y``;
val appdef = ``!x. app x  = x ``;
vval th2 = MK_ABS th1;
define_conv appdef;
define_conv predicatedef;
*)

(*
val thm = mk_thm ([``app = \x.(x + 1)``],``!x. x = 0``);
val def = hd (hyp thm);
remove_unused_def def thm;
*)
  
fun prove_final_thm hypl =
  let val thl1 = map ASSUME hypl in
  let val th1 = LIST_CONJ thl1 in
  
(* varll is a list of list of variables 
   which were instantiated in the first place 
   eqthm is provided by the conversion *)  
fun prove_initial_thm appdefl predicatedef varll eqthm finalthm =
  let val th1 = remove_bool_axioms finalthm in
  let val th2 = add_exists_thm varll thm in 
  let val (lemma1,lemma2) = EQ_IMP_RULE eqthm in
  let val lemma3 = UNDISCH lemma1 in
  let val th3 = PROVE_HYP lemma3 th2 in
  
  let val convl = (map define_conv appdefl) in
  let val th4 = remove_unused_def def thm in
  
  
  end end end end end  
    




(* Assuming we have prove the final_thm *)

   
(* test 
show_assums :=  true ;
val thm = mk_thm ([``x:bool``],``y:bool``);
val thm = mk_thm ([``(P : bool -> bool) (!x. x)``], ``y:bool``);
val thm = ASSUME term;
main thm;
bool_conv term;
beta_conv term;
eta_conv term;
normalForms.CNF_CONV term;
bool_conv term;
(bool_conv THENC normalForms.CNF_CONV) term;
fun_conv term;
app_conv term;
num_conv term;
predicate_conv term; (* to be changed *)
val term = list_mk_conj (hyp th3);
val fvdict = create_fvdict term;
val bvdict = create_fvdict term;
val cdict = create_cdict term;

val term = ``!b. P b \/ b``; 
predicate_conv term
*)

end