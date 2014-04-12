(* LIBRARIES *)
(* 
load "blibTools"; open blibTools;
load "blibExtract"; open blibExtract;
load "blibName"; open blibName;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibPrinter"; open blibPrinter;

*)

(* load all theories *)


(** **)
load "listTheory";
(* test *)
val mflag = false;
val rflag = false;
val fflag = false;



val finalgoal = (hd o fst) (BEAGLE_NF_TAC newthml goal);
val newgoal = beagle_filter path finalgoal;
metisTools.FO_METIS_TAC [] newgoal;

beagle_unsat path thml goal;


val thm = listTheory.DROP_0;
val thml = [listTheory.DROP_def];
val goal = (hyp thm, concl thm);

val path = "/tmp/HOLtoTFF";
val finalgoal = beagle_nf (thml,goal);
write_tff path finalgoal;

TAC_PROOF (goal, metisTools.METIS_TAC thml) ;

val path = "/tmp/HOLtoTFF"
val thml = map snd (DB.axioms "list" @ DB.definitions "list")
fun mk_goal thm = (hyp thm,concl thm)
val goall = map (mk_goal o snd) (DB.theorems "list")

val l = filter (beagle_unsat path thml) goall


List.length thml in