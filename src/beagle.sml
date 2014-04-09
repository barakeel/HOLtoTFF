structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     blibBtools blibMonomorph blibTactic
     blibPrinter

fun BEAGLE_ERR function message =
    HOL_ERR{origin_structure = "beagle",
	    origin_function = function,
            message = message}

val directory = "/home/gauthier/HOLtoTFF\\ workspace/HOLtoTFF/"

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

(* relevance filtering done by beagle *)
fun beagle_filter filepath hyp1 hyp2 concl =
  if hyp2 = [] then (hyp1,concl) else
    (
    beagle_interact filepath (hyp1 @ hyp2) concl; 
    if get_SZSstatus (filepath ^ "_proof") = "Unsatisfiable" 
    then beagle_filter filepath hyp1 (tl hyp2) concl 
    else beagle_filter filepath (hd hyp2 :: hyp1) (tl hyp2) concl
    )
    
fun BEAGLE_PROVE thml goal =
  let val filepath = "/tmp/HOLtoTFF" in 
  let val (mthml,_) = if is_polymorph_pb (thml,goal) then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val (finalgoall,val1) = BEAGLE_NF_TAC mthml goal in
  let val finalgoal =  hd finalgoall in
  let val dict = write_tff filepath finalgoal in
  let val newgoal = beagle_filter filepath [] (fst finalgoal) (snd finalgoal) in
    val1 [TAC_PROOF (newgoal, metisTools.FO_METIS_TAC [])]
  end end end end end end