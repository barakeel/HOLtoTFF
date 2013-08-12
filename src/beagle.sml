structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     listtools tools printtools
     higherorder monomorph tactic
     printtff printresult

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}

(* Status *)
val SZSstatus = ref "undefined"

fun update_SZSstatus filename = 
  let val SZSstatuspath = mk_SZSstatuspath filename in
  let val file = TextIO.openIn SZSstatuspath in 
  let val str = TextIO.inputAll file in
    (
    SZSstatus := str;
    TextIO.closeIn file
    )  
  end end end   

fun write_SZSstatus filename szsstatus =
  let val SZSstatuspath = mk_SZSstatuspath filename in
  let val file = TextIO.openOut SZSstatuspath in 
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
 
(* BEAGLE INTERACTION *)
fun beagle_interact filename finalgoal =
  (
  (* print the problem *)
  write_tff (mk_tffpath filename) finalgoal false
    handle _ => raise BEAGLE_ERR "write_tff" (goal_to_string finalgoal);
  (* call beagle on tffpath *)
  write_tffpath (mk_tffpath filename); 
  OS.Process.system 
          ("cd " ^ directory ^ ";" ^
           "sh " ^ directory ^ "callbeagle.sh")
    handle _ => raise BEAGLE_ERR "beagle_call" "";
  update_SZSstatus filename
  )
  
fun update_nbl1 () =
  (
  update_nb_flag nb_m mflag;
  update_nb_flag nb_fun funflag;
  update_nb_flag nb_bool boolflag;
  update_nb_flag nb_num numflag;
  update_nb_flag nb_ho hoflag
  )

fun update_nbl2 str =
  case str of
    "Unsatisfiable" => addone_nb nb_unsat
  | "Unknown" => addone_nb nb_unknown
  | "Satisfiable" => addone_nb nb_sat
  | "Time Out" => addone_nb nb_timeout
  | "Parsing failed" => addone_nb nb_parsing
  | "undefined" => addone_nb nb_codeerr
  | _ => addone_nb nb_beagerr


fun init_beagle_tac_aux filename =
  (
  show_assums := true;
  SZSstatus := "undefined";
  write_SZSstatus filename (!SZSstatus);
  app flag_off [mflag,hoflag,funflag,boolflag,numflag,metisflag];
  update_all_nb (mk_statspath filename)
  )

(* BEAGLE_TAC *)
fun beagle_tac_aux filename thml goal = 
( 
init_beagle_tac_aux filename;
addone_nb nb_problem;
  (
  flag_update mflag (exists is_polymorph_thm thml);
  flag_update_metis thml goal; 
  update_nb_flag nb_metis metisflag;
  
  let val mthml = if fst (!mflag) then monomorph_pb_c thml goal else thml in 
  let val (finalgoal_list,validation) = BEAGLE_NF_TAC mthml goal  in
                                        (* update the higher-order flag *)
  let val finalgoal = hd (finalgoal_list) in
    (
    beagle_interact filename finalgoal;                   
    flags_update_conv thml goal;
    update_nbl1 (); 
    update_nbl2 (!SZSstatus);
    if (!SZSstatus = "Unsatisfiable")
    then
      (
      write_conv filename thml goal;
      write_result (mk_resultpath filename) thml goal (!SZSstatus) 
        [!mflag,!hoflag,!funflag,!boolflag,!numflag]
      )
    else 
      (
      write_result (mk_errpath filename) thml goal (!SZSstatus)
        [!mflag,!funflag,!boolflag,!numflag,!hoflag];
      write_conv filename thml goal;
      write_tff (mk_tfferrpath filename) finalgoal true
      )
    )  
  end end end
  
  )
  handle  
    HOL_ERR {origin_structure = s, origin_function = f, message = m}
        => (
           addone_nb nb_codeerr;
           write_err filename thml goal f m; 
           write_result (mk_errpath filename) thml goal (!SZSstatus)
              [!mflag,!hoflag,!funflag,!boolflag,!numflag];
           write_conv filename thml goal
           ) 
    | _ => (
           addone_nb nb_codeerr;
           write_err filename thml goal "" "code error";
           write_result (mk_errpath filename) thml goal (!SZSstatus)
              [!mflag,!hoflag,!funflag,!boolflag,!numflag]
           ) 
;
(* stats *)
write_stats filename (!nb_problem) 
  [!nb_m,!nb_fun,!nb_bool,!nb_num,!nb_ho] 
  [!nb_unsat,!nb_unknown,!nb_sat,!nb_timeout,
   !nb_parsing,!nb_codeerr,!nb_beagerr,!nb_metis]  
;
([],fn x => (mk_thm goal)) (* always return the good result *)
)

fun BEAGLE_TAC thml goal = 
  let val filename = "beagletacresult/beagletac" in 
    beagle_tac_aux filename thml goal
  end
  

end  