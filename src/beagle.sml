structure beagle :> beagle =
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
load "higherorder"; open higherorder;
open OS.Process;
*)
open HolKernel Abbrev boolLib
     tools listtools
     higherorder monomorph conv rule printtff printresult

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}
 
(* BEAGLE PREPARE *)
(* no proof reconstruction *) 
(* use of mk_thm *)
fun beagle_firststep thml goal =
  let val terml = map concl (map DISCH_ALL thml) in
  let val th0 = mk_thm goal in 
  let val th1 = repeatchange ADD_ASSUM terml th0 in  
  let val th2 = negate_concl th1 in
  let val th3 = list_conj_hyp th2 in
    hd (hyp th3) 
  end end end end end 
  
fun beagle_monomorph term monomorphflag =
  if monomorphflag then monomorph term else term

fun beagle_conv term = 
  QCONV
  (
  normalForms.CNF_CONV THENC
  bool_conv THENC (* can create new forall *)
  fun_conv THENC (* add new constants *)
  num_conv THENC (* add => *)
  normalForms.CNF_CONV
  )
  term


fun beagle_laststep eqth =
  let val term = rhs (concl eqth) in
  let val terml = hyp eqth in
  let val th1 = 
    if null terml 
    then mk_thm ([term],F) 
    else mk_thm (terml @ [term],F) 
  in
  (* remove all existential quantifiers from all hypothesis *)
  let val th2 = remove_exists_thm th1 in 
  (* add bool_axiom *)  
  let val th3 = add_bool_axioms th2 in    
  (* app conv only if there is higher order*)
  (* should be a new name for app *)
  let val th4 =
    if firstorder_thm th3 then th3 
    else mk_thm (
         map rhs (map concl (map (app_conv "app") (hyp th3)))
         ,F)
  in    
    (eqth,(hyp th4,concl th4)) 
  end end end end end end
         
fun beagle_prepare thml goal monomorphflag =
  (* first step *)
  let val term1 = beagle_firststep thml goal in
  (* monomorphisation *)
  let val term2 = beagle_monomorph term1 monomorphflag in
  (* conversion *)
  let val eqth = beagle_conv term2 in
  (* last step *)
    beagle_laststep eqth
  end end end
   
(* path are absolute *) 
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
fun mk_holpath filename = directory ^ filename ^ "_hol"  
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_statuspath filename = directory ^ filename ^ "_tff_status"

fun beagle filename thml goal prepareflag monomorphflag =
  let val path1 = mk_tffpath filename in
  let val path2 = mk_holpath filename in
  (
  if prepareflag
  then
    let val (eqthm,finalgoal) = beagle_prepare thml goal monomorphflag in
      (
      output_result path2 thml goal eqthm true;
      output_tff path1 finalgoal;
      output_tffpath path1
      )
    end  
  else
    (
    output_result path2 thml goal (ASSUME T) false;
    output_tff path1 goal;
    output_tffpath path1
    )
  ;
  (* call beagle on tffpath and print the result in a newfile *)
  (* should read the name of the file to be excecuted somewhere 
     for example currentfilepath.txt*)
  OS.Process.system 
  ("cd " ^ directory ^ ";" ^
   "sh " ^ directory ^ "callbeagle.sh")
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
(* test 
val status = get_status "problem6";
status = "Unsatisfiable";
*)
fun beagle_tac_aux thml goal monomorphflag =
  let val filename = "default" in
  (
  beagle filename thml goal true monomorphflag
  ; 
  let val status = get_status filename in
  let fun validation thml = mk_thm goal in
    case status of
      "Unsatisfiable" => ([],validation)
    | "Satisfiable" => raise BEAGLE_ERR "BEAGLE_TAC" "Satisfiable" 
    | _ => raise BEAGLE_ERR "BEAGLE_TAC" "Error"
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
val goal = ([``x:bool``],``y:bool``);
val goal = ([``(P : bool -> bool) (!x. x)``], ``y:bool``);
val goal : goal = 
([],``(!x . x + x = 1) ==> (x = 1)``);
val goal : goal = 
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
val term = list_mk_conj (fst (goal) @ [snd goal]);
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