(* LIBRARIES *)
(* 
load "blibTactic"; open blibTactic;
load "beagle"; open beagle;
load "blibMonomorph"; open blibMonomorph; 
*)

normalForms.CNF_CONV ``A \/ ~A``;

val (finalgoall,_) = BEAGLE_NF_TAC thml goal;
BEAGLE_ORACLE thml goal;
BEAGLE_PROVE thml goal;



val thml = [];
val goal : goal = 
([``(f = (\x.(x:int) + (1:int)) ) /\ (P T)``],
``P (f (2:int) = (3:int)) : bool``);



metisTools.METIS_TAC thml goal;
metisTools.FO_METIS_TAC thml (hd finalgoall);

val (goal1,_) = (PROBLEM_TO_GOAL_TAC thml goal);
val (goal2,_) = CNF_CONV_TAC (hd goal1);
val (goal3,_) = FUN_CONV_TAC (hd goal2);
val (goal4,_) = CNF_CONV_TAC (hd goal3);
val (goal5,_) = BOOL_CONV_TAC (hd goal4);
val (goal6,_) = CNF_CONV_TAC (hd goal5);
val (goal7,_) = (
                ERASE_EXISTS_TAC THEN 
                FORALL_CONJUNCTS_TAC THEN
                STRIP_CONJ_ONLY_HYP_TAC THEN
                ERASE_FORALL_TAC
                )
                (hd goal6);
val (goal8,_) = DEFUNCT_TAC (hd goal7);
val (goal9,_) =  NUM_INT_TAC (hd goal8);
val (goal10,_) = BOOL_BV_TAC (hd goal9);
val (goal11,_) = ADD_BOOL_AXIOM_TAC (hd goal10);
;

(* Quelques preuves *)


val thml = [];
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``],F);
BEAGLE_PROVE thml goal; 

val thml = [];
val goal : goal = 
([],``((f a b = 3:int) /\ (f a = g)) ==> (g b = (2+1:int))``);
BEAGLE_PROVE thml goal;   
  

(* Exemple de la présentation *)
val goal : goal = ([],``(h (x:'a) y z :bool) /\ (h (x:'a) = g)``);
val goal : goal = ([],``P (A /\ B):bool``);
val goal : goal = ([``P (\x.x+1):bool``],F);
val goal : goal = ([``f (x:num) = (y:num)``],F);
BEAGLE_NF_TAC [] goal;
val (goall,_) = FUN_CONV_TAC goal;
val (goall,_) = NUM_INT_TAC goal;











