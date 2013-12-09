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

  
(* to be renamed *)
fun FINALGOAL_TAC_w filepath dict finalgoal =
  (* reading *)
  let val rdict = mk_rdict dict in
  let val linel = readl (filepath ^ "_proof") in
  let val proof = read_proof linel rdict in
    METIS_COOPER_BEAGLE_TAC proof finalgoal
  end end end

fun FINALGOAL_TAC filepath dict finalgoal =
  wrap "beagle" "FINALGOAL_TAC" "" 
    (FINALGOAL_TAC_w filepath dict) finalgoal




fun beagle_interact filepath finalgoal =
  (
  OS.Process.system ("cd " ^ directory ^ ";" ^
                     "sh " ^ directory ^ "callbeagle.sh " ^ filepath)
  handle _ => raise BEAGLE_ERR "beagle_interact" "OS.process.system"
  ;
  ()
  )

fun mk_cooperthml thml goal =
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
    let val rdict = mk_rdict dict in
    let val linel = readl (filepath ^ "_proof") in
    let val proof = read_proof linel rdict in
      mk_cooperthml_proof_goal proof finalgoal
    end end end
    )
  end end end end end




(* MAIN FUNCTIONS *)
fun BEAGLE_TAC_aux filepath thml goal = 
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val (finalgoall,val_finalgoal) = BEAGLE_NF_TAC mthml goal in
  let val finalgoal = hd (finalgoall) in
  let val dict = write_tff filepath finalgoal in
    (
    beagle_interact filepath finalgoal;
    let val SZSstatus = get_SZSstatus (filepath ^ "_proof") in
      if SZSstatus = "Unsatisfiable"
      then 
        let val (bgoall,val_bgoal) = FINALGOAL_TAC filepath dict finalgoal in
          (bgoall, val_finalgoal o (mk_list 1) o val_bgoal)
        end
      else raise BEAGLE_ERR "BEAGLE_TAC_aux" SZSstatus
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
    beagle_interact filepath finalgoal
  end end end end end
  
  
fun BEAGLE_TAC thml goal = 
  let val filepath = "/tmp/HOLtoTFF" in 
    BEAGLE_TAC_aux filepath thml goal
  end
 
fun BEAGLE_PROVE thml goal = TAC_PROOF (goal,BEAGLE_TAC thml) 
  
end  