structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib
     blibBtools blibMonomorph blibExtractvar blibTactic
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

(* best 15 matches *)
fun related_thms (thml,goal) theoryl = 
  let val cl1 = merge (get_cl_goal goal :: map get_cl_thm thml) in
  let fun matchable thm = 
     let val cl2 = get_cl_thm thm in
       List.length (inter cl1 cl2) >= 2
     end
  in
  let fun add_info thm =
     let val cl2 = get_cl_thm thm in (thm,List.length (inter cl1 cl2)) end
  in
  let val thml1 = map (fst o snd) (DB.matchp matchable theoryl) in
  let val thmla = map add_info thml1 in
  let fun lessa ((_,a),(_,b)) = a < b in 
  let val newthmla = quicksort lessa thmla in
    first_n 15 (map fst newthmla)
  end end end end
  end end end 

fun pb_to_term thml goal = 
  list_mk_conj
    (map (concl o GEN_ALL o DISCH_ALL) thm @ (mk_neg (snd goal) :: fst goal))

fun beagle_nf thml goal =
  let val term0 = pb_to_term thml goal in
  let val term1 = conv term0 in
  let val terml2 = conv term1 in
    (terml2,F)
  end end end  
    
fun beagle_interact filepath goal =
  (write_tff filepath goal;
  OS.Process.system ("cd " ^ directory ^ ";" ^
                     "sh " ^ directory ^ "callbeagle.sh " ^ filepath)
  handle _ => raise BEAGLE_ERR "beagle_interact" "OS.process.system")

fun beagle_unsat filepath goal =
  (beagle_interact filepath goal;
   get_SZSstatus (filepath ^ "_proof") = "Unsatisfiable")

(* relevance filtering done by beagle on top theorems *)
fun beagle_filter_aux filepath thml1 thml2 goal =
  if thml2 = [] then (thml1,concl) else
    if (beagle_unsat filepath ((thml1 @ (tl thml2)),concl) handle _ => false)
    then beagle_filter_aux filepath thml1 (tl thml2) concl 
    else beagle_filter_aux filepath (hd thml2 :: thml1) (tl thml2) concl

fun beagle_filter filepath goal = 
  if not (beagle_unsat filepath goal) then goal 
  else beagle_filter_aux filepath [] (fst goal) (snd goal)
    
fun BEAGLE_PROVE thml goal =
  (* basic lemma mining *)
  let val newthml = related_thms (thml,goal) [] in
  let val filepath = "/tmp/HOLtoTFF" in 
  (* monomorphisation *)
  let val (mthml,_) = if is_polymorph_pb (newthml,goal) 
                      then monomorph_pb (newthml,goal) 
                      else (newthml,goal)
  in
  let val finalgoal = beagle_nf mthml goal in
  let val newgoal = beagle_filter filepath finalgoal in
    val1 [TAC_PROOF (newgoal, metisTools.FO_METIS_TAC [])]
  end end end end end end
  
end