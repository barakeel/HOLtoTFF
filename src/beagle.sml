structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     blibBtools blibSyntax
     blibExtractvar
     blibHO blibMonomorph blibTactic
     blibPrinttff blibReader
     beaglePrintresult beagleStats

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}


fun start_ctime ctime =
  ctime := Time.toMilliseconds (Time.now())
  
fun end_ctime ctime =
  let val fin = Time.toMilliseconds (Time.now()) in
    ctime := fin - (!ctime)
  end

(* STATUS *)
val SZSstatus = ref "Undefined"

fun update_SZSstatus filename = 
  let val proofpath = mk_proofpath filename in
  let val strl = readl proofpath in
    case strl of
      [] => SZSstatus := "Undefined"
    | [a] => SZSstatus := "Undefined"
    | a :: b :: m => SZSstatus := String.substring (b,13,(String.size b) - 14)
  end end

fun write_SZSstatus filename szsstatus =
  let val proofpath = mk_proofpath filename in
  let val file = TextIO.openOut proofpath in 
    TextIO.output (file,szsstatus)
  end end
  
(* BEAGLE_NF *)               
fun BEAGLE_NF_TAC thml goal =
  (
  PROBLEM_TO_GOAL_TAC thml THEN
  BEAGLE_CONV_TAC THEN
  BEAGLE_CLAUSE_SET_TAC
  )
  goal 


fun step_to_string (cl,n) =
  (Int.toString n) ^ " : " ^ (term_to_string cl)
fun proof_to_stringl proof = map step_to_string proof

  
(* BEAGLE INTERACTION *)
fun beagle_interact filename finalgoal =
  (* print the problem *)
  (
  start_ctime impctime;
  let 
    val dict = write_tff (mk_tffpath filename) (!nb_problem) finalgoal false
  in
    (
    end_ctime impctime;
    (* call beagle on tffpath *)
    write_tffpath (mk_tffpath filename); 
    OS.Process.system 
      ("cd " ^ directory ^ ";" ^
       "sh " ^ directory ^ "callbeagle.sh")
      handle _ => raise BEAGLE_ERR "beagle_call" "";
    update_SZSstatus filename
    (*(* replaying the proof *)
    let val filename1 = filename ^ "_declaration" in
    let val filename2 = filename ^ "_reading" in
    let val filename3 = filename ^ "_proving" in
    (* reading *)
    let val rtyadict = mk_rtyadict (#1 dict) in
    let val rvdict = mk_rvdict (#3 dict) (#4 dict) in
    let val rdict = (mk_rtyadict (#1 dict),mk_rvdict (#3 dict) (#4 dict)) in
    let val linel = readl (filename ^ "_tff_proof") in
      (* axiom *)
    let val hypl = fst finalgoal in
    let val axioml = read_axioml linel rdict in
    let val thmaxioml = map (PROVE_AXIOM hypl) axioml in
      (* proof *)
    let val proof = read_proof (format_proof linel) rdict in
      (
      writel filename1 ["(* Type dictionnary *)"];
      writell filename1 (map fst rtyadict) (map (type_to_string o snd) rtyadict);
      writel filename1 ["(* Variables dictionnary *)"];
      writell filename1 (map fst rvdict) (map (term_to_string o snd) rvdict);
      writel filename2 ["(* Axioms *)"];
      writel filename2 (map term_to_string axioml);
      writel filename2 ["(* Proof *)"];
      writel filename2 (proof_to_stringl proof);
      writel filename2 ["(* Proven Axioms *)"];
      writel filename2 (map thm_to_string thmaxioml);
      PROVE_PROOF filename3 thmaxioml proof
      )
    end end end end
    end end end end 
    end end end;
    ()
    *)
    )
  end
  )
  
fun init_beagle_tac_aux filename =
  (
  show_assums := true;
  SZSstatus := "Undefined";
  write_SZSstatus filename (!SZSstatus);
  reset_allflag ();
  reset_all_nb ();
  update_all_nb (mk_statspath filename);
  metctime := 0; beactime := 0; tractime := 0; impctime := 0
  )

(* BEAGLE_TAC *)
fun write_goodresult filename thml goal =
  write_result (mk_resultpath filename) thml goal (!nb_problem) (!SZSstatus) 
    (allflag_value ())

fun write_badresult filename thml goal =
  write_result (mk_errpath filename) thml goal (!nb_problem) (!SZSstatus) 
    (allflag_value ())

fun updateadd_nb nb n = nb := (fst(!nb) + n, snd (!nb))

fun addone_faultl () =
  (
  addone_nb (list_nth 0 faultl);
  if fst(!hoflag) 
  then addone_nb (list_nth 1 faultl)
  else addone_nb (list_nth 2 faultl);
  if fst(!mflag) 
  then addone_nb (list_nth 3 faultl)
  else addone_nb (list_nth 4 faultl);
  if fst (!numflag)
  then addone_nb (list_nth 5 faultl)
  else addone_nb (list_nth 6 faultl)
  )


 
fun update_4timers n =
  (
  updateadd_nb (list_nth n timerl) (!metctime);  
  updateadd_nb (list_nth (n + 1) timerl) (!beactime);
  updateadd_nb (list_nth (n + 2) timerl) (!tractime);
  updateadd_nb (list_nth (n + 3) timerl) (!impctime)
  )

fun update_timerl () =
  (
  update_4timers 0;
  if fst(!hoflag) then update_4timers 4 else update_4timers 8;
  if fst(!mflag)  then update_4timers 12 else update_4timers 16;
  if fst (!numflag) then update_4timers 20 else update_4timers 24
  )
 
fun metis_test thml goal = 
  (
  start_ctime metctime;
  metisTools.METIS_TAC thml goal;
  end_ctime metctime
  )
  handle _ => flag_update metisflag true
 
fun beagle_tac_aux filename thml goal = 
  (
  init_beagle_tac_aux filename;
  addone_nb nb_problem;
    (
    flag_update mflag (is_polymorph_pb (thml,goal));
    start_ctime tractime;
    start_ctime beactime;
    let val (mthml,mgoal) = if is_polymorph_pb (thml,goal)
                            then monomorph_pb (thml,goal) 
                            else (thml,goal)
    in
    let val (finalgoal_list,validation) = BEAGLE_NF_TAC mthml mgoal  in
                                        (* update all flags *)
    let val finalgoal = hd (finalgoal_list) in
      (
      end_ctime tractime;
      flag_update proofflag
        (is_subset_goal (mk_goal (validation [mk_thm finalgoal])) goal);
        beagle_interact filename finalgoal;
        end_ctime beactime;
        if (!SZSstatus) = "Unsatisfiable" 
        then 
          (
          metis_test thml goal;
          update_timerl ()
          )
        else ();
        update_nbl1 (); 
        update_nbl2 (!SZSstatus);
        if (!SZSstatus) = "Unsatisfiable"
        then write_goodresult filename thml goal
        else 
          (addone_faultl ();
          write_badresult filename thml goal;
           write_tff (mk_tfferrpath filename) (!nb_problem) finalgoal true;
           ()
         )
      ) 
    end end end
  )
  handle  
    HOL_ERR {origin_structure = s, origin_function = f, message = m}
        => (
           addone_nb nb_codeerr;
           write_err (mk_errpath filename) s f m; 
           write_badresult filename thml goal
           ) 
    | _ => (
           addone_nb nb_codeerr;
           write_err (mk_errpath filename) "" "" "code error";
           write_badresult filename thml goal
           ) 
  ; 
  write_stats filename (map ! nb_all); 
  ([],fn x => (mk_thm goal))
  )

(* MAIN FUNCTION *)
fun BEAGLE_TAC thml goal = 
  let val filename = "beagletacresult/beagletac" in 
    beagle_tac_aux filename thml goal (* test arithmetic *)
  end
  

end  