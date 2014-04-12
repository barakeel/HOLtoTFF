structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib blibTools blibExtract 
     blibConv blibMonomorph blibPrinter

val directory = "/home/gauthier/HOLtoTFF\\ workspace/HOLtoTFF/"

fun get_SZSstatus proofpath = 
  let val strl = readl proofpath in
    case strl of
      [] => raise B_ERR "get_SZSstatus" "not found"
    | [a] => raise B_ERR "get_SZSstatus" "not found"
    | a :: b :: m => String.substring (b,13,(String.size b) - 14)
                     handle _ => raise B_ERR "get_SZSstatus" "not found"
  end

(* Basic lemma mining (15 best matches) *)
fun related_thms (thml,goal) theoryl = 
  let val cl1 = merge (map get_cl (snd goal :: fst goal) @ map get_cl_thm thml) in
  let fun matchable thm = 
     let val cl2 = get_cl_thm thm in
       concl thm <> snd goal andalso List.length (intersect cl1 cl2) >= 1
     end
  in
  let fun add_info thm =
     let val cl2 = get_cl_thm thm in (thm,List.length (intersect cl1 cl2)) end
  in
  let val thml1 = map (fst o snd) (DB.matchp matchable theoryl) in
  let val thmla = map add_info thml1 in
  let fun lessa (_,a) (_,b) = a < b in 
  let val newthmla = sort lessa thmla in
    first_n 15 (map fst newthmla)
  end end end end
  end end end 

(* Normalization *)
fun pb_to_term (thml,goal) = 
  list_mk_conj (map (concl o GEN_ALL o DISCH_ALL) thml @ 
               (mk_neg (snd goal) :: fst goal) )
fun mk_clever_forall bvl t = list_mk_forall (intersect (free_vars t) bvl,t)

fun beagle_nf (thml,goal) =
  let val term0 = pb_to_term (thml,goal) in
  let val term1 = (rhs o concl) (QCONV normalForms.CNF_CONV term0) in
  let val term2 = repeat rw_absbool term1 in
  let val term3 = (rhs o concl) (QCONV normalForms.CNF_CONV term2) in
  let val term4 = (rhs o concl) (QCONV APP_CONV term3) in
  let val (_,term5) = strip_exists term4 in
  let val (bvl,term6) = strip_forall term5 in
  let val term7l = strip_conj term6 in   
  let val terml8 = map (mk_clever_forall bvl) term7l in 
  let val terml9 = map (rhs o concl o (QCONV BOOL_BV_CONV)) terml8 in
    (terml9,F)
  end end end end end 
  end end end end end 
    
fun beagle_interact path goal =
  (
  write_tff path goal;
  OS.Process.system ("cd " ^ directory ^ ";" ^
                     "sh " ^ directory ^ "callbeagle.sh " ^ path)
  handle _ => raise B_ERR "beagle_interact" "OS.process.system"
  )

fun beagle_unsat path thml goal =
  (
  let val finalgoal = beagle_nf (thml,goal) in beagle_interact path finalgoal end;
  get_SZSstatus (path ^ "_proof") = "Unsatisfiable"
  )

(* Relevance filtering *)
fun beagle_filter_aux path thml1 thml2 goal =
  if null thml2 then (thml1,goal) 
  else
    if beagle_unsat path (thml1 @ (tl thml2)) goal handle _ => false
    then beagle_filter_aux path thml1 (tl thml2) goal 
    else beagle_filter_aux path (hd thml2 :: thml1) (tl thml2) goal


fun beagle_filter path (thml,goal) = 
  if not (beagle_unsat path thml goal) 
  then raise B_ERR "BEAGLE_PROVE" "Proof not found"
  else beagle_filter_aux path [] thml goal
 
(* Main function *)    
fun BEAGLE_PROVE rflag mflag thml goal =
  let val path = "/tmp/HOLtoTFF" in 
  let val rthml = if rflag then related_thms (thml,goal) [] else thml in
  let val (mthml,_) = if is_polymorph_pb (rthml,goal) andalso mflag 
                      then monomorph_pb (rthml,goal) 
                      else (rthml,goal)
  in
  let val (fthml,_) = beagle_filter path (mthml,goal) in
    TAC_PROOF (goal, metisTools.METIS_TAC fthml) 
  end end end end
  
end