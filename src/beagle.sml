structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib blibTools blibExtract 
     blibConv blibMonomorph blibPrinter

(* Global path *)
val directory = "/home/gauthier/HOLtoTFF\\ workspace/HOLtoTFF/"
val tffpath = "/tmp/HOLtoTFF"

fun get_SZSstatus proofpath = 
  let val strl = readl proofpath in
    case strl of
      [] => raise B_ERR "get_SZSstatus" "not found"
    | [a] => raise B_ERR "get_SZSstatus" "not found"
    | a :: b :: m => String.substring (b,13,(String.size b) - 14)
                     handle _ => raise B_ERR "get_SZSstatus" "not found"
  end

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

(* Beagle *)   
fun BEAGLE_TAC thml goal =
  let val (mthml,_) = if is_polymorph_pb (thml,goal)
                      then monomorph_pb (thml,goal) 
                      else (thml,goal)
  in
  let val finalgoal = beagle_nf (mthml,goal) in 
    (
    write_tff tffpath goal;
    OS.Process.system ("cd " ^ directory ^ ";" ^
                       "sh " ^ directory ^ "callbeagle.sh " ^ tffpath)
    handle _ => raise B_ERR "BEAGLE_TAC" "OS.process.system";
    if get_SZSstatus (tffpath ^ "_proof") = "Unsatisfiable" 
    then ([],fn _ => mk_thm goal)
    else raise B_ERR "BEAGLE_TAC" (get_SZSstatus (tffpath ^ "_proof"))
    )
  end end

end