structure beagle :> beagle =
struct

open HolKernel Abbrev boolLib blibTools blibExtract 
     blibConv blibMonomorph blibPrinter normalForms

(* Global path *)
val directory = "/home/gauthier/HOLtoTFF\\ workspace/HOLtoTFF/"
val tffpath = "/tmp/HOLtoTFF"

fun get_SZSstatus_aux strl = 
  case strl of
    [] => "Unreadable"
  | a :: m => (let val l = String.tokens Char.isSpace a  in
                if hd l = "SZS" andalso hd (tl l) = "status"
                then hd (tl (tl l))
                else if hd l = "Execution" andalso hd (tl l) = "interrupted"
                then "Time out"
                else get_SZSstatus_aux m 
               end
               handle _ => get_SZSstatus_aux m)

   
fun get_SZSstatus () = get_SZSstatus_aux (readl (tffpath ^ "_status")) 
                       handle _ => "File not found"

(* Normalization *)
fun pb_to_term (thml,goal) = 
  list_mk_conj (
    [mk_neg (snd goal)] @ (fst goal) @ map concl thml
  )       
fun mk_clever_forall bvl t = list_mk_forall (intersect (free_vars t) bvl,t)

fun rw conv term = (rhs o concl) (QCONV conv term)

(* alternative CNF_CONV without extensionality simplification *)
val ALT_SIMPLIFY_CONV = SIMP_CONV (simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss)) []
val ALT_NNF_CONV = ALT_SIMPLIFY_CONV THENC PURE_NNF_CONV
val ALT_CNF_CONV = ALT_NNF_CONV THENC
                   SKOLEMIZE_CONV THENC
                   PRENEX_CONV THENC
                   PURE_CNF_CONV

fun beagle_nf (thml,goal) =
  let val term1 = pb_to_term (thml,goal) in
  let val term2 = repeat (rw_absbool o (rw ALT_SIMPLIFY_CONV)) term1 in
  let val term3 = rw ALT_CNF_CONV term2 in
  let val term4 = rw APP_CONV term3 in
  let val (_,term5) = strip_exists term4 in
  let val (bvl,term6) = strip_forall term5 in
  let val term7l = strip_conj term6 in   
  let val terml8 = map (mk_clever_forall bvl) term7l in 
  let val terml9 = map (rw BOOL_BV_CONV) terml8 in
    (terml9,F)
  end end end end end 
  end end end end 

(* Beagle *)   
fun BEAGLE_TAC thml goal =
  let val ithml = map (GEN_ALL o DISCH_ALL) thml in
  let val (mthml,_) = if is_polymorph_pb (ithml,goal)
                      then monomorph_pb (ithml,goal) 
                      else (ithml,goal)
  in
  let val finalgoal = beagle_nf (mthml,goal) in 
    (
    write_tff tffpath finalgoal;
    OS.Process.system ("cd " ^ directory ^ ";" ^
                       "sh " ^ directory ^ "callbeagle.sh " ^ tffpath)
    handle _ => raise B_ERR "BEAGLE_TAC" "OS.process.system";
    if get_SZSstatus () = "Theorem" 
    then ([],fn _ => mk_thm goal)
    else raise B_ERR "BEAGLE_TAC" (get_SZSstatus ())
    )
  end end end

end