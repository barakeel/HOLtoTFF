structure blibBconv :> blibBconv =
struct

open HolKernel Abbrev boolLib blibDatatype
     blibBtools blibBrule

fun BCONV_ERR function message =
  HOL_ERR {origin_structure = "blibBconv",
	         origin_function = function,
           message = message}

fun REPEAT_N_CONV n conv = 
  case n of
    0 => ALL_CONV
  | n => if n < 0 then raise BCONV_ERR "REPEAT_N_CONV" ""  
         else
           conv THENC REPEAT_N_CONV (n - 1) conv

fun not_strip_exists_conv term =
  let val n = length (fst (strip_exists (dest_neg term))) in
    REPEAT_N_CONV n (STRIP_QUANT_CONV NOT_EXISTS_CONV) term
  end  

fun strip_forall_not_conv term = 
  if is_forall term 
  then ((LAST_FORALL_CONV FORALL_NOT_CONV) THENC strip_forall_not_conv) term
  else raise UNCHANGED
 
fun ARG_CONV conv term =
  if structterm term = Comb 
  then (RAND_CONV conv THENC RATOR_CONV (ARG_CONV conv)) term 
  else raise UNCHANGED 
 
  
(* FORALL_CONJUNCTS_CONV *)
fun forall_conjuncts_conv_w term = 
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
fun forall_conjuncts_conv term = 
  wrap "blibClauseset" "forall_conjuncts_conv" "" forall_conjuncts_conv_w term  
  
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val thm = ASSUME term;
show_assums := true;
*)

end