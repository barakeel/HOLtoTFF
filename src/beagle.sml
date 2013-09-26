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
  let 
    val dict = write_tff (mk_tffpath filename) (!nb_problem) finalgoal false
  in
    (
    (* call beagle on tffpath *)
    write_tffpath (mk_tffpath filename); 
    OS.Process.system 
      ("cd " ^ directory ^ ";" ^
       "sh " ^ directory ^ "callbeagle.sh")
      handle _ => raise BEAGLE_ERR "beagle_call" "";
    update_SZSstatus filename;
    (* replaying the proof *)
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
    )
  end
  
fun init_beagle_tac_aux filename =
  (
  show_assums := true;
  SZSstatus := "Undefined";
  write_SZSstatus filename (!SZSstatus);
  reset_allflag ();
  update_all_nb (mk_statspath filename)
  )

(* BEAGLE_TAC *)
fun write_goodresult filename thml goal =
  write_result (mk_resultpath filename) thml goal (!nb_problem) (!SZSstatus) 
    (allflag_value ())

fun write_badresult filename thml goal =
  write_result (mk_errpath filename) thml goal (!nb_problem) (!SZSstatus) 
    (allflag_value ())
 
fun beagle_tac_aux filename thml goal = 
  (
  init_beagle_tac_aux filename;
  addone_nb nb_problem;
    (
    flag_update mflag (is_polymorph_pb (thml,goal));
    let val (mthml,mgoal) = if is_polymorph_pb (thml,goal)
                            then monomorph_pb (thml,goal) 
                            else (thml,goal)
    in 
    let val (finalgoal_list,validation) = BEAGLE_NF_TAC mthml mgoal  in
                                        (* update all flags *)
    let val finalgoal = hd (finalgoal_list) in
      (
      flag_update proofflag
        (is_subset_goal (mk_goal (validation [mk_thm finalgoal])) goal);
        beagle_interact filename finalgoal;
        update_nbl1 (); 
        update_nbl2 (!SZSstatus);
        if (!SZSstatus) = "Unsatisfiable"
        then write_goodresult filename thml goal
        else 
          (write_badresult filename thml goal;
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
  write_stats filename (!nb_problem) (map ! nb_list1) (map ! nb_list2); 
  ([],fn x => (mk_thm goal))
  )

(* MAIN FUNCTION *)
fun BEAGLE_TAC thml goal = 
  let val filename = "beagletacresult/beagletac" in 
    beagle_tac_aux filename thml goal (* test arithmetic *)
  end
  

end  