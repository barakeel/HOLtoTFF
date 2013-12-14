structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     blibBtools blibMonomorph blibTactic
     blibPrinter blibReader

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}

val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"

fun get_SZSstatus proofpath = 
  let val strl = readl proofpath in
    case strl of
      [] => raise BEAGLE_ERR "get_SZSstatus" "not found"
    | [a] => raise BEAGLE_ERR "get_SZSstatus" "not found"
    | a :: b :: m => String.substring (b,13,(String.size b) - 14)
                       handle _ => raise BEAGLE_ERR "get_SZSstatus" "not found"
  end
            
fun BEAGLE_NF_TAC thml goal =
  (
  PROBLEM_TO_GOAL_TAC thml THEN
  BEAGLE_CONV_TAC THEN
  BEAGLE_CLAUSE_SET_TAC
  )
  goal 

fun beagle_interact filepath finalgoal =
  OS.Process.system ("cd " ^ directory ^ ";" ^
                     "sh " ^ directory ^ "callbeagle.sh " ^ filepath)
  handle _ => raise BEAGLE_ERR "beagle_interact" "OS.process.system"

fun BEAGLE_ORACLE thml goal =
  let val filepath = "/tmp/HOLtoTFF" in 
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val finalgoal = (hd o fst) (BEAGLE_NF_TAC mthml goal) in
  let val dict = write_tff filepath finalgoal in
    (
    beagle_interact filepath finalgoal;
    let val SZSstatus = get_SZSstatus (filepath ^ "_proof") in
      if SZSstatus = "Unsatisfiable" 
      then mk_thm goal (* mk_thm only used here *)
      else raise BEAGLE_ERR "BEAGLE_ORACLE" SZSstatus 
    end
    )
  end end end end
  
fun beagle_proof thml goal =
  let val filepath = "/tmp/HOLtoTFF" in 
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val finalgoal = (hd o fst) (BEAGLE_NF_TAC mthml goal) in
  let val dict = write_tff filepath finalgoal in
    (
    beagle_interact filepath finalgoal;
    let val SZSstatus = get_SZSstatus (filepath ^ "_proof") in
      if SZSstatus = "Unsatisfiable" 
      then read_proof (filepath ^ "_proof") dict
      else raise BEAGLE_ERR "BEAGLE_PROOF" SZSstatus
    end
    )
  end end end end


 
end  