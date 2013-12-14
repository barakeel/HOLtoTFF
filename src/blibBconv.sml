structure blibBconv :> blibBconv =
struct

open HolKernel Abbrev boolLib blibDatatype
     blibBtools blibBrule blibSyntax

fun BCONV_ERR function message =
  HOL_ERR {origin_structure = "blibBconv",
	         origin_function = function,
           message = message}


fun STRIP_FORALL_NOT_CONV term = 
  if is_forall term 
  then ((LAST_FORALL_CONV FORALL_NOT_CONV) THENC STRIP_FORALL_NOT_CONV) term
  else raise UNCHANGED
 
fun ARG_CONV conv term =
  if structterm term = Comb 
  then (RAND_CONV conv THENC RATOR_CONV (ARG_CONV conv)) term 
  else raise UNCHANGED 
 
fun LIST_FUN_EQ_CONV vl term =
  case vl of
    [] => raise UNCHANGED
  | [v] => X_FUN_EQ_CONV v term
  | v :: m => ((X_FUN_EQ_CONV v) THENC 
              (STRIP_QUANT_CONV (LIST_FUN_EQ_CONV m))) 
              term  
 
(* FORALL_CONJUNCTS_CONV *)
(* tools *)
fun unconj_hyp_rule term thm =
  if is_conj term then
    let val th0 = ASSUME (lhand term) in
    let val th1 = ASSUME (rand term) in
    let val th2 = CONJ th0 th1 in
      PROVE_HYP th2 thm
    end end end 
  else raise BCONV_ERR "unconj_hyp_rule" ""

fun list_unconj_hyp_rule hypl thm = repeat_change unconj_hyp_rule hypl thm
  
fun strip_conj_hyp_rule thm =
  case filter is_conj (hyp thm) of
    [] => thm
  | l => strip_conj_hyp_rule (list_unconj_hyp_rule l thm)

(* main *)
fun FORALL_CONJUNCTS_CONV_w term = 
  let val (bvl,t) = strip_forall term in
  (* first part *)
  let val th10 = ASSUME term in
  let val th11 = SPECL bvl th10 in
  let val thl12 = CONJUNCTS th11 in
  let val thl13 = map (GENL bvl) thl12 in
  let val th14 = LIST_CONJ thl13 in
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th20 = ASSUME (concl th14) in
  let val th21 = ASSUME t in
  let val th22 = strip_conj_hyp_rule th21 in
  let val thl23 = CONJUNCTS th20 in
  let val thl24 = map (SPECL bvl) thl23 in
  let val th25 = LIST_PROVE_HYP thl24 th22 in
  let val th26 = GENL bvl th25 in 
  let val th27 = DISCH (concl th14) th26 in
  (* together *)
    IMP_ANTISYM_RULE th15 th27
  end end end end end 
  end end end end end 
  end end end end end
fun FORALL_CONJUNCTS_CONV term = 
  wrap "blibClauseset" "FORALL_CONJUNCTS_CONV" "" FORALL_CONJUNCTS_CONV_w term  
  
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
*)

(* INTEGER NORMALISATION *)
fun land_int_normatom_conv atom =
  (
  LAND_CONV
  (
  (ONCE_DEPTH_CONV OmegaMath.sum_normalise) THENC
  (ONCE_REWRITE_CONV [integerTheory.INT_MUL_LID]) THENC
  (ONCE_REWRITE_CONV [STRIP_SYM integerTheory.INT_NEG_MINUS1]) THENC
  REWRITE_CONV [integerTheory.INT_ADD_LID, integerTheory.INT_ADD_RID]
  )
  atom
  )
  handle _ => raise UNCHANGED
 
fun rand_int_normatom_conv atom =
  (
  RAND_CONV
  (
  (ONCE_DEPTH_CONV OmegaMath.sum_normalise) THENC
  (ONCE_REWRITE_CONV [integerTheory.INT_MUL_LID]) THENC
  (ONCE_REWRITE_CONV [STRIP_SYM integerTheory.INT_NEG_MINUS1]) THENC
  REWRITE_CONV [integerTheory.INT_ADD_LID, integerTheory.INT_ADD_RID]
  )
  atom
  )
  handle _ => raise UNCHANGED

fun norm_eq_conv term =
  if is_eq term 
  then 
    if less_term ((lhs term),(rhs term))
    then raise UNCHANGED
    else SYM (REFL term)
  else raise UNCHANGED

fun int_normatom_conv atom =
  if (is_eq atom orelse intSyntax.is_less atom orelse intSyntax.is_leq atom orelse
     intSyntax.is_great atom orelse intSyntax.is_geq atom)
  then
   (land_int_normatom_conv THENC rand_int_normatom_conv THENC norm_eq_conv) atom
  else raise UNCHANGED

fun INT_NORM_CLAUSE_CONV term = 
  let val (_,atom) = strip_forall term in
    if is_neg atom
    then STRIP_QUANT_CONV (RAND_CONV int_normatom_conv) term
    else STRIP_QUANT_CONV int_normatom_conv term
  end


end