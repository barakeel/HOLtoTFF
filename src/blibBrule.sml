structure blibBrule :> blibBrule =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools

fun BRULE_ERR function message =
  HOL_ERR {origin_structure = "blibBrule",
	         origin_function = function,
           message = message}

fun CONV_RULE conv thm = EQ_MP (QCONV conv (concl thm)) thm  

fun CONV_HYPO_RULE conv term thm =
  let val (_,lemma) = EQ_IMP_RULE (QCONV conv term) in
    PROVE_HYP (UNDISCH lemma) thm
  end
 
fun CONV_HYPL_RULE conv terml thm = repeat_change (CONV_HYPO_RULE conv) terml thm 
 
fun list_PROVE_HYP thml thm =
  case thml of
    [] => thm
  | th :: m => list_PROVE_HYP m (PROVE_HYP th thm)  

fun list_conj_hyp_rule thm =
  let val hyptl = hyp thm in
  let val t1 = list_mk_conj hyptl in
  let val thl = CONJ_LIST (length hyptl) (ASSUME t1) in
  let val th2 = list_PROVE_HYP thl thm in
    th2
  end end end end   

(* disjunction *)
fun list_DISJ_CASES_UNION term thml =
  if not (length (strip_disj term) = length thml) 
  then raise BRULE_ERR "LIST_DISJ_CASES" "wrong number of theorems"
  else
    if length (strip_disj term) = 1 
    then hd thml
    else
      let val (term1,term2) = dest_disj term in
        DISJ_CASES_UNION (ASSUME term) 
        (hd thml) (list_DISJ_CASES_UNION term2 (tl thml)) 
      end

(* assume there is only one hypothesis *)
fun unconj_hyp_rule term thm =
  if is_conj term then
    let val th0 = ASSUME (lhand term) in
    let val th1 = ASSUME (rand term) in
    let val th2 = CONJ th0 th1 in
      PROVE_HYP th2 thm
    end end end 
  else raise BRULE_ERR "unconj_hyp_rule" ""

(* hypl is a list of conj *)
fun list_unconj_hyp_rule hypl thm = repeat_change unconj_hyp_rule hypl thm
  
fun strip_conj_hyp_rule thm =
  case filter is_conj (hyp thm) of
    [] => thm
  | l => strip_conj_hyp_rule (list_unconj_hyp_rule l thm)

fun list_AP_THM thm terml =
  case terml of
    [] => thm 
  | t :: m => list_AP_THM (AP_THM thm t) m 

(* input is an equality *)
fun list_FUN_EQ_CONV vl term =
  case vl of
    [] => raise UNCHANGED
  | [v] => X_FUN_EQ_CONV v term
  | v :: m => ((X_FUN_EQ_CONV v) THENC 
              (STRIP_QUANT_CONV (list_FUN_EQ_CONV m))) 
              term 
   
fun repeat_rule n rule thm =   
  case n of
    0 => thm
  | _ => if n < 0 then raise BRULE_ERR "repeat_rule" ""
         else rule (repeat_rule (n - 1) rule thm) 
         
fun EXTL bvl thm =
  case rev bvl of
    [] => thm
  | bv :: m => let val th0 = SPECL bvl thm in
                 EXTL (rev m) ( GENL (rev m) (EXT (GEN bv th0)) )  
               end             

fun list_TRANS eqthml =
  case eqthml of
    [] => raise BRULE_ERR "list_TRANS" "no argument"
  | [eqthm] => eqthm
  | eqthm :: m => TRANS eqthm (list_TRANS m) 

(* remove def *)
fun remove_def def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end

fun remove_defl defl thm = repeat_change remove_def defl thm


end