structure blibBtactic :> blibBtactic =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype
     blibSyntax blibBrule blibBconv

fun BTACTIC_ERR function message =
  HOL_ERR {origin_structure = "blibBtactic",
	         origin_function = function,
           message = message}


(* TAC BUILDER *)
fun mk_tac1_aux goalbuilder valbuilder goal =
  let val goall = [goalbuilder goal] in
  let val validation = fn [thm] => valbuilder goal thm  
                       | _     => raise BTACTIC_ERR "mk_tac1" 
                                        "list length is not one"           
  in
    (goall,validation)
  end end

fun mk_tac1 goalbuilder valbuilder goal = 
  VALID (mk_tac1_aux goalbuilder valbuilder) goal 


(* CONV_HYP_TAC *) 
fun conv_hyp conv goal =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val terml = erase_double_aconv (map (rhs o concl) eqthl) in
    (terml,snd goal)
  end end
  
fun conv_hyp_val conv goal thm =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val allhyp = merge_aconv (map hyp eqthl) in
    if null allhyp then 
      let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
      let val th0 = list_PROVE_HYP lemmal thm in
        th0
      end end
    else raise BTACTIC_ERR "conv_hyp_val" "no hypothesis allowed"
  end end 
   
fun CONV_HYP_TAC conv goal =
  mk_tac1 (conv_hyp conv) (conv_hyp_val conv) goal

(* list_ASSUME_TAC *)
fun list_ASSUME_TAC thml goal =
  case thml of
    [] => ALL_TAC goal
  | thm :: m => ((ASSUME_TAC thm) THEN (list_ASSUME_TAC m)) goal
  
(* REMOVE_HYPL_TAC *) 
fun REMOVE_HYPL_TAC hypl goal = 
  let fun remove_hypl hypl goal =
    (filter (not o (inv is_member_aconv hypl)) (fst goal), snd goal) 
  in
  let fun remove_hypl_val hypl goal thm = repeat_change ADD_ASSUM hypl thm 
  in
    mk_tac1 (remove_hypl hypl) (remove_hypl_val hypl) goal
  end end  
 
 
  
end