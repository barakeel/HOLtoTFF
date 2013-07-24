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
 
(* tools *)
fun is_polymorph term = not (null (all_vartype term)) 
fun is_polymorph_goal =   
  exists is_polymorph (fst goal) orelse
  is polymorph (snd goal)
fun is_polymorph_thm = 
  exists is_polymorph (hyp thm) orelse
  is polymorph (concl thm)
fun is_polymorph_pb thml goal =
  exists is_polymorph_thm thml orelse
  is polymorph_goal goal 


fun list_TRANS eqthml =
  case eqthml of
    [] => raise BEAGLE_ERR "list_TRANS" "no argument"
  | [eqthm] => eqthm
  | eqthm :: m => TRANS eqthm (list_TRANS m)
  
    
(* end tools *) 
 
 
 
(* BEAGLE PREPARE *)

(* use of mk_thm *)
fun beagle_firststep thml goal =
  let val th0 = mk_thm goal in
    rule thml th0
  end  



fun list_add_assum = repeatchange ADD_ASSUM;

fun rule thml thm =
  let val th0 = list_add_assum (map concl (map DISCH_ALL thml)) thm in
  let val th1 = negate_concl th0 in
  let val th2 = list_conj_hyp th1 in
    th2
  end end end
     
(* thm should have a false conclusion * and a negated conclusion *)
fun validation nhyp thml goal thm = 
  let val th0 = conj_list_hyp nhyp thm in
  let val th1 = DISCH (mk_neg snd(goal)) th0 in
  let val th2 = list_prove_hyp (map DISCH_ALL thml) th1 in
  let val th3 = CCONTR goal in
  let val th4 = list_add_assum (fst goal) th3 in
    th4
  end end end end end
    
(* use of goal*)  
   
   

fun beagle_conv pps term = 
  let val eqth1 = QCONV normalForms.CNF_CONV term in
  let val term1 = rhs (concl eqth1) in 
    (
    if not(term1 = term)
    then (add_string pps "CNF1: "; print_thm pps eqth1; add_newline pps)
    else ();
  let val eqth2 = QCONV fun_conv term1 in  
  let val term2 = rhs (concl eqth2) in
    if not(term2 = term1)
    then (add_string pps "Lambda: "; print_thm pps eqth2; add_newline pps)
    else ();
  let val eqth3 = QCONV bool_conv term2 in
  let val term3 = rhs (concl eqth3) in
    if not(term3 = term2)
    then (add_string pps "Boolean: "; print_thm pps eqth3; add_newline pps)
    else ();
  let val eqth4 = QCONV num_conv term3 in
  let val term4 = rhs (concl eqth4) in
    if not(term4 = term3)
    then (add_string pps "Numeral: "; print_thm pps eqth4; add_newline pps)
    else ();
  let val eqth5 = QCONV normalForms.CNF_CONV term4 in
  let val term5 = rhs (concl eqth5) in
    if not(term5 = term4) 
    then (add_string pps "CNF2: " print_thm pps eqth5; add_newline pps)
    else ();
  list_TRANS [eqth1,eqth2,eqth3,eqth4,eqth5]
  )
  end end end end end 
  end end end end end   


fun beagle_laststep pps eqth =
  let val term = rhs (concl eqth) in
  let val terml = hyp eqth in
  let val th1 = 
    if null terml 
    then mk_thm ([term],F) 
    else mk_thm (terml @ [term],F) 
  in
  (* remove all existential quantifiers from all hypothesis *)
  let val th2 = remove_exists_thm th1 in 
    (
    if not (th1 = th2)
    then (add_string pps "Exists: " print_thm pps th2; add_newline pps)
    else (); 
  (* add bool_axiom *)  
    let val th3 = add_bool_axioms th2 in
      if not (th2 = th3)
      then add_string pps "Boolaxiom: " print_thm pps th2; add_newline pps)
      else () 
    end;  
  (* higher order (erase some important hypothesis) *)
  let val th4 =
    if firstorder_thm th3 then th3 
    else 
      let val appname = create_newname_thm "app" th3 in
      let val hypl = map rhs (map concl (map (app_conv appname) (hyp th3))) in
        mk_thm (hypl,F)
      end end
  in        
    (hyp th4,concl th4) 
  end end end end end end
     
             
fun beagle_prepare pps thml goal mflag =
  (* print goal and thml *)
  (
  pp_goal pps goal;
  pp_thml pps thml;
  (* first step *)
  let val term1 = hyp (beagle_firststep thml goal) in 
  (* monomorphisation *)
  let val term2 = if mflag
                  then (add_string pps " mono" ; monomorph term2)
                  else term2
  in
  (* conversion *)
  let val eqth = beagle_conv term2 in
  (* last step *)
    beagle_laststep eqth 
  end end end
  ) 
   
   
fun get_status filename = 
  let val statuspath = mk_statuspath filename in
  let val file = TextIO.openIn (statuspath) in 
  let val status = TextIO.inputAll file in
    (
    TextIO.closeIn file;
    status
    )  
  end end end   
   
(* path are absolute *) 
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
fun mk_holpath filename = directory ^ filename ^ "_hol"  
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_statuspath filename = directory ^ filename ^ "_tff_status"
fun mk_bigrespath filename = direcotry ^ filename ^ "_bigres"
fun mk_adresspath () = directory ^ "filepath.txt"

fun beagle filename thml goal mflag =
  (
  let val bigrespath = mk_bigrespath filename in
  let val bigfile = TextIO.openAppend bigrespath in 
  let val bigpps = PP.mk_ppstream in 
  
  let val smallrespath = mk_smallrespath filename in
  let val smallfile = TexIO.openAppend smallrespath in
  let val smallpps = PP.mk_ppstream in
    
  let val path1 = mk_tffpath filename in
  let val path2 = mk_holpath filename in
  let val adresspath = mk_addresspath () in
  let val finalgoal = beagle_prepare bigpps thml goal mflag in
    ( 
    (* print the problem *)
    output_tff path1 finalgoal; 
    output_path addresspath path1; 
    (* call beagle on tffpath*)
    OS.Process.system 
    ("cd " ^ directory ^ ";" ^
     "sh " ^ directory ^ "callbeagle.sh");
    
    let val status = get_status filename in
      (
      (* short result *)
      add_string smallpps ((substring (status,0,3)) ^ " : ")
      pp_goal smallpps goal; 
      add_newline smallpps;
      (* big result *)
      add_string bigpps ("Status : " ^ status);
      add_newline bigpps
      )
    end
    )
  end end end end end 
  end end end end end





(* close the files *)





(* test 
val status = get_status "problem6";
status = "Unsatisfiable";
*)

fun beagle_tac_aux thml goal mflag =
  let val filename = "default" in
  (
  beagle filename thml goal mflag
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
  if is_polymorph_pb thml goal 
  then
    beagle_tac_aux thml goal false
    handle _ => beagle_tac_aux thml goal true
  else 
    beagle_tac_aux thml goal false
    
  
  
  
  
   

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