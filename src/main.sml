structure main :> main =
struct
(* 
load "listtools"; open listtools;
load "tools"; open tools;
load "extractvar"; open extractvar;
load "nametype"; open nametype;
load "namevar"; open namevar;
load "conv"; open conv; 
load "rule"; open rule; 
load "printtff"; open printtff;
load "printresult";open printresult;
load "monomorph"; open monomorph;
open Abbrev;
open OS.Process;
*)
open HolKernel Abbrev
     tools listtools
     monomorph conv rule printtff printresult

fun MAIN_ERR function message =
    HOL_ERR{origin_structure = "main",
	    origin_function = function,
            message = message}
 

(* CONV *)
(* could translate to a clause set with only forall quantifier *)  
fun main_conv term = 
  QCONV
  (
  beta_conv THENC
  (* eta_conv THENC *)
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
  )
  term

(* BEAGLE PREPARE *)
(* no monomorphisation *)
(* no proof reconstruction *) 
(* use of mk_thm *)
(* thml is not used for now *)
fun beagle_prepare thml goal monomorphflag =
  let val terml = map concl (map DISCH_ALL thml) in
  let val th0 = mk_thm goal in 
  let val th0_1 = repeatchange ADD_ASSUM terml th0 in  
  let val th1 = negate_concl th0_1 in
  let val th2 = list_conj_hyp th1 in
  let val term1 = hd (hyp th2) in
  (* monomorphisation *)
  let val term2 = 
    if monomorphflag then monomorph term1 else term1
  in
  (* conversion *)
  let val eqth = main_conv term2 in
  let val term3 = rhs term2 in
  let val th3 = mk_thm ([term3],F) in
  (* remove all existential quantifiers from all hypothesis *)
  let val th4 = remove_exists_thm th3 in 
  (* add bool_axiom *)  
  let val th5 = add_bool_axioms th4 in   
    (eqth,(hyp th5,concl th5))
   end end end end end 
   end end end end end
   end end

(* path *) 
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
fun mk_holpath filename = directory ^  "result/"  ^ filename ^ "_hol"  
fun mk_tffpath filename = directory ^  "result/"  ^ filename ^ "_tff" 
fun mk_statuspath filename = directory ^ "result/" ^ filename ^ "_tff_status"

fun main filename thml initgoal prepareflag monomorphflag =
  let val path1 = mk_tffpath filename in
  let val path2 = mk_holpath filename in
  (
  if prepareflag
  then
    let val (eqthm,finalgoal) = beagle_prepare thml initgoal monomorphflag in
      (
      output_tff path1 finalgoal;
      output_result path2 thml initgoal finalgoal eqthm true;
      output_tffpath directory path1
      )
    end  
  else
    (
    output_tff path1 initgoal;
    output_result path2 thml initgoal ([T],T) (ASSUME T) false;
    output_tffpath directory path1
    )
  ;
  (* call beagle on tffpath and print the result in a newfile *)
  (* should read the name of the file to be excecuted somewhere 
     for example currentfilepath.txt*)
  OS.Process.system ("sh callbeagle.sh")
  )
  end end

fun get_status filename = 
  let val statuspath = mk_statuspath filename in
  let val file = TextIO.openIn (statuspath) in 
  let val status = TextIO.inputAll file in
    (
    TextIO.closeIn file;
    status
    )  
  end end end 

fun beagle_tac_aux thml goal monomorphflag =
  let val filename = "default" in
  (
  main filename thml goal true monomorphflag
  ; 
  let val status = get_status filename in
  let fun validation thml = mk_thm goal in
    case status of
      "CounterSatisfiable" => ([],validation)
    | "Satisfiable" => raise MAIN_ERR "BEAGLE_TAC" "Satisfiable" 
    | _ => raise MAIN_ERR "BEAGLE_TAC" "Error"
  end end 
  )
  end

fun BEAGLE_TAC thml goal =
  (* without monomorphisation *)
  beagle_tac_aux thml goal false
  (* with monomorphisation *)
  handle _ => beagle_tac_aux thml goal true
   

(* test 
show_assums :=  true ;
val initgoal = ([``x:bool``],``y:bool``);
val initgoal = ([``(P : bool -> bool) (!x. x)``], ``y:bool``);
val initgoal : goal = 
([],``(!x . x + x = 1) ==> (x = 1)``);
val initgoal : goal = 
([],``(!x. x + x = 1) ==> (y = 1)``);
val filename = "problem1";   
val thml = [];
val prepareflag = false;
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
val term = list_mk_conj (fst (initgoal) @ [snd initgoal]);
val fvdict = create_fvdict term;
val bvdict = create_bvdict term;
val cdict = create_cdict term;
*)  

(* PROOF RECONSTRUCTION WIP 
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