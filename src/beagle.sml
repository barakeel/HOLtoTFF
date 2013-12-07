structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     blibBtools blibSyntax blibBtactic
     blibExtractvar
     blibHO blibMonomorph blibTactic
     blibPrinttff blibReader blibReplayer

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}

val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"

(* STATUS *)
fun get_SZSstatus proofpath = 
  let val strl = readl proofpath in
    case strl of
      [] => raise BEAGLE_ERR "get_SZSstatus" "not found"
    | [a] => raise BEAGLE_ERR "get_SZSstatus" "not found"
    | a :: b :: m => String.substring (b,13,(String.size b) - 14)
                       handle _ => raise BEAGLE_ERR "get_SZSstatus" "not found"
  end

(* BEAGLE NORMAL FORM *)               
fun BEAGLE_NF_TAC_w thml goal =
  (
  PROBLEM_TO_GOAL_TAC thml THEN
  BEAGLE_CONV_TAC THEN
  BEAGLE_CLAUSE_SET_TAC
  )
  goal 

fun BEAGLE_NF_TAC thml goal = 
  wrap "beagle" "BEAGLE_NF_TAC" "" (BEAGLE_NF_TAC_w thml) goal 

fun step_to_string (cl,n) =
  (Int.toString n) ^ " : " ^ (term_to_string cl)
fun proof_to_stringl proof = map step_to_string proof

  
(* BEAGLE INTERACTION *)
fun PROVE_FINAL_GOAL_w filepath dict finalgoal =
  (* reading *)
  let val rdict = mk_rdict dict in
  let val linel = readl (filepath ^ "_proof") in
  (* axiom *)
  let val hypl = fst finalgoal in
  let val (axioml,proof) = read_proof linel rdict in
  (* proof debugging *)
  let val filepath1 = filepath ^ "_declaration" in
  let val filepath2 = filepath ^ "_reading" in
  let val filepath3 = filepath ^ "_replaying" in 
    (
    writel filepath1 ["(* Type dictionnary *)"];
    appendll filepath1 (map fst (#1 rdict)) (map (type_to_string o snd) (#1 rdict));
    writel filepath1 ["(* Variables dictionnary *)"];
    appendll filepath1 (map fst (#2 rdict)) (map (term_to_string o snd) (#2 rdict));
    writel filepath2 ["(* Axioms *)"];
    appendl filepath2 (map term_to_string axioml);
    appendl filepath2 ["(* Proof *)"];
    appendl filepath2 (proof_to_stringl proof);
    let val thmaxioml = map (PROVE_AXIOM hypl) axioml in
    (print "\nAXIOMS PROVEN\n";
    PROVE_PROOF filepath3 thmaxioml proof
    )
    end
    )
  end end end end
  end end end 

fun PROVE_FINAL_GOAL filepath dict finalgoal =
  wrap "beagle" "PROVE_FINAL_GOAL" "" (PROVE_FINAL_GOAL_w filepath dict) finalgoal

fun beagle_interact_w filepath finalgoal =
  (
  OS.Process.system ("cd " ^ directory ^ ";" ^
                     "sh " ^ directory ^ "callbeagle.sh " ^ filepath)
    handle _ => raise BEAGLE_ERR "beagle_interact" "OS.process.system";
  ()
  )


fun beagle_interact filepath finalgoal =
  wrap "beagle" "beagle_interact" "" (beagle_interact_w filepath) finalgoal

(* MAIN FUNCTIONS *)
fun beagle_tac_aux filepath thml goal = 
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val (finalgoall,validation_nf) = BEAGLE_NF_TAC mthml goal in
  let val finalgoal = hd (finalgoall) in
  let val dict = write_tff filepath finalgoal in
    (
    beagle_interact filepath finalgoal;
    let val SZSstatus = get_SZSstatus (filepath ^ "_proof") in
      if SZSstatus = "Unsatisfiable"
      then 
        let fun validation _ = 
          validation_nf [PROVE_FINAL_GOAL filepath dict (hd finalgoall)]   
        in 
          ([], validation)
        end
      else raise BEAGLE_ERR "beagle_tac_aux" SZSstatus
    end
    ) 
  end end end end

fun BEAGLE_ORACLE thml goal =
  let val filepath = "/tmp/HOLtoTFF" in 
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val (finalgoall,validation_nf) = BEAGLE_NF_TAC mthml goal in
  let val finalgoal = hd (finalgoall) in
  let val dict = write_tff filepath finalgoal in
    (
    beagle_interact filepath finalgoal;
    print ( (get_SZSstatus (filepath ^ "_proof")) ^ "\n")
    )
  end end end end end
  
  
fun BEAGLE_TAC thml goal = 
  let val filepath = "/tmp/HOLtoTFF" in 
    beagle_tac_aux filepath thml goal
  end
 
fun BEAGLE_PROVE thml goal = TAC_PROOF (goal,(BEAGLE_TAC thml)) 
  
end  