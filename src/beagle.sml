structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib HOLPP 
     listtools freshvar tools
     namevar
     higherorder monomorph conv rule printtff printresult

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}
 
(* tools *)
fun is_polymorph term = not (null (all_vartype term)) 
fun is_polymorph_goal goal =   
  exists is_polymorph (fst goal) orelse
  is_polymorph (snd goal)
fun is_polymorph_thm thm = 
  exists is_polymorph (hyp thm) orelse
  is_polymorph (concl thm)
fun is_polymorph_pb thml goal =
  exists is_polymorph_thm thml orelse
  is_polymorph_goal goal 

fun list_TRANS eqthml =
  case eqthml of
    [] => raise BEAGLE_ERR "list_TRANS" "no argument"
  | [eqthm] => eqthm
  | eqthm :: m => TRANS eqthm (list_TRANS m) 
(* end tools *) 
 
(* BEAGLE PREPARE *)

(* create a term which will be transformed *)
fun thml_to_hypterm thml = 
  concl (LIST_CONJ (map DISCH_ALL thml))

fun goal_to_hypterm goal =
  if null (fst goal) 
  then mk_neg (snd goal)
  else mk_conj (list_mk_conj (fst goal),mk_neg (snd goal))

fun problem_to_hypterm thml goal =
  if null thml 
  then goal_to_hypterm goal
  else mk_conj (thml_to_hypterm thml,goal_to_hypterm goal)

(* proof 


fun goalhyp_lemma goal = 
  let val terml = fst goal in
  let val thml = map ASSUME terml in
    LIST_CONJ thml
  end end 
  
fun list_add_assum terml thm = repeatchange ADD_ASSUM terml thm  
 
 *) 
(* PROOF  
(* thm has form term => F term has the form created by problem *)
fun finalrule thml goal thm = 
  let val lemma1 = LIST_CONJ (map DISCH_ALL thml) in
  let val th0 = map UNDISCH thm in
  let val th3 = 
    if null thml 
    then th0 
    else 
      let val th1 = unconj_hyp (hd (hyp th0)) th0 in
      let val th2 = PROVE_HYP lemma1 th1 in
        if null (hyp th22) (* can happen because hyp is a set *)
        then ADD_ASSUM (goal_to_hypterm goal) th2
        else th2
      end end 
  in
    if null (fst goal) 
    then CCONTR goal th3
    else 
      let val th4 = unconj_hyp (hd (hyp th3)) th3 in     
      let val th5 = CCONTR goal th4 in         
      let val th6 = PROVE_HYP (goalhyp_lemma goal) in
      let val th7 = list_add_assum (hyp goal) in 
        th7
      end end end end
  end end end        
*)  
    
(* conv *)   
fun beagle_conv pps term = 
  let val eqth1 = QCONV normalForms.CNF_CONV term in
  let val term1 = rhs (concl eqth1) in (
    if not(term1 = term)
    then (add_string pps "CNF1: "; 
          add_string pps (term_to_string term1);
          add_newline pps)
    else ();
  let val eqth2 = QCONV fun_conv term1 in  
  let val term2 = rhs (concl eqth2) in (
    if not(term2 = term1)
    then (add_string pps "Lambda: ";
          add_string pps (term_to_string term2);
          add_newline pps)
    else ();
  let val eqth3 = QCONV bool_conv term2 in
  let val term3 = rhs (concl eqth3) in (
    if not(term3 = term2)
    then (add_string pps "Boolean: ";
          add_string pps (term_to_string term3);
          add_newline pps)
    else ();
  let val eqth4 = QCONV num_conv term3 in
  let val term4 = rhs (concl eqth4) in (
    if not(term4 = term3)
    then (add_string pps "Numeral: "; 
          add_string pps (term_to_string term4);
          add_newline pps)
    else ();
  let val eqth5 = QCONV normalForms.CNF_CONV term4 in
  let val term5 = rhs (concl eqth5) in (
    if not(term5 = term4) 
    then (add_string pps "CNF2: "; 
          add_string pps (term_to_string term5);
          add_newline pps)
    else ();
    list_TRANS [eqth1,eqth2,eqth3,eqth4,eqth5]
  ) end end 
  ) end end 
  ) end end 
  ) end end 
  ) end end   

(* last step *)
fun beagle_clauseset term =
  let val (bvl,t) = strip_exists term in 
  let val eqth = forall_conjuncts_conv t in
  let val term1 = rhs (concl eqth) in
  let val terml2 = strip_conj term1 in
  (* erase unused quantifier *)
  let val terml3 = map (rhs o concl o (QCONV normalForms.CNF_CONV)) terml2 in 
  (* add axioms should add suc axioms *)  
  let val boolaxterm = concl (CONJUNCT1 BOOL_EQ_DISTINCT) in
  let val terml4 = if exists has_boolarg terml3
                   then boolaxterm :: terml3 
                   else terml3 
  in
  (* higher order *)
  let val terml4 =
    if firstorder (list_mk_conj terml3)
    then terml3 
    else 
      let val appname = list_create_newname "app" terml3 in
        map rhs (map concl (map (QCONV (app_conv appname)) (terml3))) 
      end 
  in        
    terml4
  end end end 
  end end end
  end end

(* test 
val term = ``x = 0 /\ y = 0``;
*)

(* PROOF *)
(* thm should start with only app extensionnal definition in hypothesis *)  
(*
fun remove_unused_app thm =  
  let val th0 = conv_hypl def_conv (hyp thm) thm in
  let val th1 = remove_unused_defl (hyp th0) th0 in
    th1
  end end
*)
(* thm has form terml3 |- F *)
(* should return the theorem term |- F *)
  
(*
fun beagle_clauseset_rule appname term terml2 thm =  
  (* remove higher order *)
  let val th0 =
    if all firstorder terml2
    then thm
    else 
      let val eqthl = map (QCONV (app_conv appname) terml2) in
      let val thl1 = map fst (map EQ_IMP_RULE eqthl) in 
      (* remove unused app *)
      let val thl2 = (map remove_unused_app thl1) in
        list_prove_hyp thl2 thm
      end end end 
  (* remove axioms *)
  let val th1 = list_prove_hyp [CONJUNCT1 BOOL_EQ_DISTINCT] th0 in
  (* regroup forall *)
  forall_conjuncts_conv term1
  (* add existential need to memorize this*)  
  add_exists ebvl thm
*)
   
 (* NO PROOF for now *)                         
fun beagle_nf pps thml goal mflag =
  (
  ppres_problem pps thml goal;
  (* transform the problem into a term *)
  let val term1 = problem_to_hypterm thml goal in 
  (* monomorphisation *)
  let val term2 = 
    if mflag
    then (add_string pps "Monomorphisation: ";  
          add_string pps (term_to_string (monomorph term1));
          add_newline pps; 
          monomorph term1)
    else term1
  in
  (* conversion cnf + bool + num + abs *)
  let val eqth = beagle_conv pps term2 in
  let val term3 = rhs (concl eqth) in
  (* clause set + app *)
    beagle_clauseset term3
  end end end end
  ) 
   
(* BEAGLE MAIN *)   
(* path are absolute *) 
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
val SZSstatus = ref "undefined"
fun mk_holpath filename = directory ^ filename ^ "_hol"  
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_SZSstatuspath filename = directory ^ filename ^ "_tff_SZSstatus"
fun mk_smallrespath filename = directory ^ filename ^ "_smallres"
fun mk_bigrespath filename = directory ^ filename ^ "_bigres"
fun mk_addresspath () = directory ^ "filepath.txt"
fun mk_tffsavepath filename = directory ^ filename ^ "_tffsave"

fun update_SZSstatus filename = 
  let val SZSstatuspath = mk_SZSstatuspath filename in
  let val file = TextIO.openIn SZSstatuspath in 
  let val str = TextIO.inputAll file in
    (
    SZSstatus := str;
    TextIO.closeIn file
    )  
  end end end   

 
 
fun beagle filename thml goal mflag =
  let val bigrespath = mk_bigrespath filename in
  let val bigfile = TextIO.openAppend bigrespath in 
  let val bigpps =
    mk_ppstream
    {
    consumer  = fn s => TextIO.output (bigfile,s),
    linewidth = 80,
    flush     = fn () => TextIO.flushOut bigfile
    } 
  in 
  (* path *)
  let val tffpath = mk_tffpath filename in
  let val tffsavepath = mk_tffsavepath filename in
  let val addresspath = mk_addresspath () in
  (* main and big results *)
    (
    begin_block bigpps CONSISTENT 0;
      let val terml = beagle_nf bigpps thml goal mflag in
      let val finalgoal = (terml,``F``) in
        ( 
        (* print the problem *)
        output_tffgoal tffpath finalgoal false; 
        output_tffgoal tffsavepath finalgoal true;
        output_tffgoalpath addresspath tffpath; 
        (* call beagle on tffpath*)
        OS.Process.system 
          ("cd " ^ directory ^ ";" ^
           "sh " ^ directory ^ "callbeagle.sh")
        )
      end end;
      update_SZSstatus filename; 
      add_string bigpps ("Status: " ^  (!SZSstatus)); 
      add_string bigpps "\n"; add_string bigpps "\n";
      (* output a short result *)
      let val smallrespath = mk_smallrespath filename in
        output_smallresult smallrespath goal (!SZSstatus) mflag
      end;  
    end_block bigpps;
    TextIO.closeOut bigfile
    )
  end end end end end 
  end 

(* test 
update_SZSstatus "problem6";
(!SZSstatus) = "Unsatisfiable";
*)
(* BEAGLE_TAC *)
fun BEAGLE_TAC thml goal =
  let val filename = "beagletacresult/beagletac" in
  let fun validation thml = mk_thm goal in
    if is_polymorph_pb thml goal 
    then
      (
      beagle filename thml goal false; 
      case (!SZSstatus) of
        "Unsatisfiable" => ([],validation)
      | _ => (beagle filename thml goal true; ([],validation)) 
      )
    else
      (
      beagle filename thml goal false; 
      ([],validation)
      )
  handle _ =>   
    (
    let val path = mk_smallrespath filename in
    let val file = TextIO.openAppend path in 
      (TextIO.output (file, "Error in SML code: \n"); TextIO.closeOut file) 
    end end;
    ([],validation)
    )
  end end
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