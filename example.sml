(* LIBRARIES *)
(* 
load "blibTactic"; open blibTactic;
load "beagle"; open beagle;
load "blibMonomorph"; open blibMonomorph; *)

(* Step by step translation *)
val thml = [];
val goal : goal = ([],
``?P f. ((f = \x.x + 1) /\ (P T)) 
         ==> P (f 0 = 1)``);

val (goal1,_) = (PROBLEM_TO_GOAL_TAC thml goal);
val (goal2,_) = CNF_CONV_TAC (hd goal1);
val (goal3,_) = FUN_CONV_TAC (hd goal2);
val (goal4,_) = CNF_CONV_TAC (hd goal3);
val (goal5,_) = BOOL_CONV_TAC (hd goal4);
val (goal6,_) = CNF_CONV_TAC (hd goal5);
val (goal7,_) = NUM_CONV_TAC (hd goal6);
val (goal8,_) = CNF_CONV_TAC (hd goal7);
val (goal9,_) = (ERASE_EXISTS_TAC THEN 
                FORALL_CONJUNCTS_TAC THEN
                STRIP_CONJ_ONLY_HYP_TAC THEN
                ERASE_FORALL_TAC THEN 
                ADD_BOOL_AXIOM_TAC) (hd goal8);
val (goal10,_) = ADD_HIGHER_ORDER_TAC (hd goal9);
val (goal11,_) = 
 (ADD_FNUM_AXIOMS_TAC THEN 
  BOOL_BV_TAC THEN 
  ADD_BOOL_AXIOM_TAC) (hd goal10);

BEAGLE_TAC thml goal;

(* Set theory example *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);

BEAGLE_TAC thml goal;











