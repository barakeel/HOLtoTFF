structure blibBrule :> blibBrule =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools

fun BRULE_ERR function message =
  HOL_ERR {origin_structure = "blibBrule",
	         origin_function = function,
           message = message}


fun conv_concl conv thm =
  let val conclt = concl thm in
  let val eqthm = conv conclt in
    EQ_MP eqthm thm
  end end     
  handle UNCHANGED => thm
  
fun conv_onehyp conv term thm =
  let val eqth1 = conv term in
  let val (lemma1,lemma2) = EQ_IMP_RULE eqth1 in
  let val lemma3 = UNDISCH lemma2 in
  let val th3 = PROVE_HYP lemma3 thm in
    th3
  end end end end 
  handle UNCHANGED => thm
 
fun conv_hypl conv terml thm = repeatchange (conv_onehyp conv) terml thm 
 
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
fun list_unconj_hyp_rule hypl thm = repeatchange unconj_hyp_rule hypl thm
  
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
                 EXTL (rev m) ( GENL(rev m) (EXT (GEN bv th0)) )  
               end             

fun list_TRANS eqthml =
  case eqthml of
    [] => raise BRULE_ERR "list_TRANS" "no argument"
  | [eqthm] => eqthm
  | eqthm :: m => TRANS eqthm (list_TRANS m) 

(************ REMOVE UNUSED DEF OR EXTENTIONAL DEF ***********)
(* remove unused def *)
fun remove_unused_def_w def thm = 
  let val th1 = DISCH def thm in
  let val th2 = GEN (lhs def) th1 in
  let val th3 = SPEC (rhs def) th2 in
  let val axiom1 = REFL (rhs def) in
  let val th4 = MP th3 axiom1 in
    th4
  end end end end end
fun remove_unused_def def thm =
  wrap "blibBrule" "remove_unused_def" "" 
    (remove_unused_def_w def) thm  

fun remove_unused_defl defl thm = repeatchange remove_unused_def defl thm

(* remove unused extdef *)
(* extdef_conv *)
fun extdef_conv_w term =
  let val (bvl,t) = strip_forall term in
  let val abs = list_mk_abs (bvl,rhs t) in
  let val term1 = list_mk_comb (abs,bvl) in
  let val eqth = (REDEPTH_CONV BETA_CONV) term1 in
  (* first part *)
  let val th10 = ASSUME term in
  let val th11 = SPECL bvl th10 in
  let val th12 = TRANS th11 (SYM eqth) in
  let val th13 = GENL bvl th12 in
  let val th14 = EXTL bvl th13 in
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th20 = ASSUME (concl th14) in
  let val th21 = list_AP_THM th20 bvl in
  let val th22 = conv_concl (RAND_CONV (REDEPTH_CONV BETA_CONV)) th21 in
  let val th23 = GENL bvl th22 in
  let val th24 = DISCH (concl th14) th23 in
  (* together *)
    IMP_ANTISYM_RULE th15 th24
  end end end end end 
  end end end end end 
  end end end end end 
fun extdef_conv term = 
  wrap "blibBrule" "extdef_conv" "" extdef_conv_w term  

fun remove_unused_extdefl_w extdefl thm =  
  let val th0 = conv_hypl extdef_conv extdefl thm in
    remove_unused_defl (map (rhs o concl o extdef_conv) extdefl) th0 
  end
  
fun remove_unused_extdefl appl thm =
  wrap "blibBrule" "remove_unused_extdefl" "" 
    (remove_unused_extdefl_w appl) thm   



end