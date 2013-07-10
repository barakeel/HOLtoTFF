structure main :> main =
struct
(* 
load "normalize"; open normalize; 
load "printtff"; open printtff;
load "nametype"; open nametype;
*)


open HolKernel 
     normalize printtff

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
  bool_conv THENC
  normalForms.CNF_CONV THENC
  fun_conv THENC
  app_conv THENC
  num_conv THENC
  predicate_conv
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


(* should output a theorem but printtff should be rewritten *)
(* MAIN *)
fun main thm = 
   let val th1 = negate_concl thm in
   let val th2 = list_conj_hyp th1 in
   let val term = hd (hyp th2) in
   let val eqth1 = convert term in
   let val (lemma1,lemma2) = EQ_IMP_RULE eqth1 in
   let val lemma3 = UNDISCH lemma2 in
   let val th3 = PROVE_HYP lemma3 th2 in
     output_tff testlocation th3
   end end end end end end end
   
(* 
load "normalize"; open normalize; 
load "printtff"; open printtff;
load "namevar"; open namevar;
*)
  
  
   
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

(* if you have an hypothesis in a conv it's not a problem *)
(*
A B C |- F
et
D |- B <=> (D => B')
 B' |- D => B'
A D => B' C D |-F
A B' C D |- F
*)
normalForms.CNF_CONV ``!x. (x = y) /\ !x. (x = y)``
(* should make dictionnaries *)
(* free_var x_str *)
(* bound X_str *)
(* constant c_str *)
(* created bool b0 or B0*)
(* created fonction f0 or F0 *)
(* created app0 ... *)
(* skolem constant printed sk0_str *)
(* should create different names for every different constant created 
, reduce after if there's two of the same constant appearing with the same name *)
(* same definition  at the same level *) 



end