structure blibBtactic :> blibBtactic =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype
     blibSyntax blibBrule blibBconv

fun BTACTIC_ERR function message =
  HOL_ERR {origin_structure = "blibBTactic",
	         origin_function = function,
           message = message}

(* TAC BUILDER *)
fun mk_tac1 goalbuilder valbuilder goal =
  let val goal_list = [goalbuilder goal] in
  let val validation = fn [thm] => valbuilder goal thm  
                       | _     => raise BTACTIC_ERR "mk_tac1" 
                                        "list length should be one"           
  in
    (
    (* this line is to be removed if you are sure about every tactics *)
    validation_test (validation [mk_thm (hd goal_list)]) goal 
    ("mk_tac1:" ^ goal_to_string (hd goal_list));
    (goal_list,validation)
    )
  end end

(* CONV_HYP_TAC *) 
fun conv_hypg conv goal =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val terml = erase_double_aconv (map (rhs o concl) eqthl) in
    (terml,snd goal)
  end end
  
fun conv_hyp_val conv goal thm =
  let val eqthl = map (QCONV conv) (fst goal) in
  let val allhyp = List.concat (map hyp eqthl) in
    if null allhyp then 
      let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
      let val th0 = list_PROVE_HYP lemmal thm in
        th0
      end end
    else raise BTACTIC_ERR "conv_hyp_val" "no hypothesis allowed"
  end end 
   
fun CONV_HYP_TAC conv goal =
  mk_tac1 (conv_hypg conv) (conv_hyp_val conv) goal

(* list_ASSUME_TAC *)
fun list_ASSUME_TAC_w thml goal =
  case thml of
    [] => ALL_TAC goal
  | thm :: m => ((ASSUME_TAC thm) THEN (list_ASSUME_TAC_w m)) goal
fun list_ASSUME_TAC thml goal =     
  wrap "tactic" "list_ASSUME_TAC" "" list_ASSUME_TAC_w thml goal
  
  
end