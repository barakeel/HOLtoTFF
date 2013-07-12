structure main :> main =
struct
(* 
load "listtools"; open listtools;
load "tools"; open tools;
load "extractvar"; open extractvar;
load "nametype"; open nametype;
load "conv"; open conv; 
load "rule"; open rule; 
load "printtff"; open printtff;
*)
open HolKernel 
     tools
     conv rule printtff

fun MAIN_ERR function message =
    HOL_ERR{origin_structure = "main",
	    origin_function = function,
            message = message}
 
(* output address *) 
val beagleproblemlocation =
  "/home/thibault/Desktop/Scalaproject/beagleproject/problem.p"
val testlocation = 
  "/home/thibault/Desktop/SMLproject/HOLtoTFF/output.txt" 
 
(* MONOMORPHISATION *)

(* CONV *)
(* could translate to a clause set with only forall quantifier *)  
fun main_conv term = 
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


(* BEAGLE CALL *)
(* no monomorphisation *)
(* no proof reconstruction *) 
(* use of mk_thm *)
(* thml is not used for now *)
(* DISCH_ALL all of them and add them to assumptions *)

fun beagle_prepare thml goal =
  let val th0 = mk_thm goal in (* TO BE REMOVED *)
  let val th1 = negate_concl th0 in
  let val th2 = list_conj_hyp th1 in
  (* conversion *)
  let val term = hd (hyp th2) in
  let val th3 = rewrite_conv_hyp main_conv term th2 in
  (* remove all existential quantifiers from all hypothesis *)
  let val th4 = remove_exists_thm th3 in 
  (* add bool_axiom *)  
  let val th5 = add_bool_axioms th4 in   
    (hyp th5,concl th5)
   end end end end end 
   end end 


(* test 
show_assums :=  true ;
val goal = ([``x:bool``],``y:bool``);
val goal = ([``(P : bool -> bool) (!x. x)``], ``y:bool``);
val goal = ([``y: bool ``],``(!x:num . (x:num) + (x:num) = 1) ==> (x = 1)``);
beagle_prepare [] goal;
output_tff testlocation goal;
*)

(* conv test
val term = hd (hyp (list_conj_hyp (negate_concl (mk_thm goal))));
normalForms.CNF_CONV term;
bool_conv (rhs (concl it));
fun_conv (rhs (concl it));
val term = (rhs (concl it));

find_free_app term;
find_bound_app term;

app_conv (rhs (concl it));
num_conv (rhs (concl it));
predicate_conv (rhs (concl it));
*)

(* dictionnary test 
val term = list_mk_conj (hyp th3);
val fvdict = create_fvdict term;
val bvdict = create_fvdict term;
val cdict = create_cdict term;
*)  

(* PROOF RECONSTRUCTION
 WIP 
(* thml is user provided for now and not used *)
fun beagle_tac


fun beagle_prove thml goal =
  
(*
val thm = mk_thm ([``app = \x.(x + 1)``],``!x. x = 0``);
val def = hd (hyp thm);
remove_unused_def def thm;
*)
  
fun prove_final_thm hyptl =
  let val thl1 = map ASSUME hyptl in
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
*)    




end