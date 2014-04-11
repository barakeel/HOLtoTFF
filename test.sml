(* LIBRARIES *)
(* 
load "blibBtools"; open blibBtools;
load "blibTffsyntax"; open blibTffsyntax ;
load "blibFreshvar"; open blibFreshvar;
load "blibSyntax"; open blibSyntax;

load "numSyntax"; open numSyntax;
load "intSyntax"; open intSyntax;

load "blibExtractvar"; open blibExtractvar;
load "int_arithTheory"; open int_arithTheory;
load "blibBtactic"; open blibBtactic;
load "blibTactic"; open blibTactic;
load "blibNumInt"; open blibNumInt;
load "blibReader"; open blibReader;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibBrule"; open blibBrule;
load "beagle"; open beagle;
*)

(* load all theories *)


(** **)
load "listTheory";

(* test *)
val thm = listTheory.DROP_NIL;
val thml = [];
val goal = (hyp thm, concl thm);

BEAGLE_PROVE thml goal;


val finalgoal = (hd o fst) (BEAGLE_NF_TAC newthml goal);
val newgoal = beagle_filter filepath finalgoal;
metisTools.FO_METIS_TAC [] newgoal;



 
 