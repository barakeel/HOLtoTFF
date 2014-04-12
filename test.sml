(* LIBRARIES *)
(* 
load "blibTools"; open blibTools;
load "blibExtract"; open blibExtract;
load "blibName"; open blibName;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibPrinter"; open blibPrinter;
load "beagle"; open beagle;
*)
(* load all theories *)
(** **)



(* test *)
val mflag = false;
val rflag = false;
val fflag = false;

val newgoal = beagle_filter path finalgoal;
metisTools.FO_METIS_TAC [] newgoal;


val path = "/tmp/HOLtoTFF"
BEAGLE_ORACLE path thml goal;
beagle_tff path finalgoal;
get_SZSstatus (path ^ "_proof") = "Unsatisfiable";

val thm = listTheory.DROP_0;
val thml = [listTheory.DROP_def];
val goal = (hyp thm, concl thm);


val finalgoal = beagle_nf (thml,goal);

(* testing dependencies on a small library *)
load "complexTheory"; 
val thml = map snd (DB.definitions "complex")
fun mk_goal thm = (hyp thm,concl thm)
val goall = map (mk_goal o snd) (DB.theorems "complex")
val goall = first_n 100 goall;
(* Done by beagle *)
val l = filter (BEAGLE_ORACLE 0 0 thml) goall
TAC_PROOF (goal, metisTools.METIS_TAC thml) ;


val thml = first_n 10 (map snd (DB.axioms "list" @ DB.definitions "list"));
val goal :goal = ([],``2 >= 0``);

val thml = [];
val goal : goal = ([``f 2 = 3``, ``~ (2 = 3)``], ``~ ((\x.x) = (f : num-> num))``);

val finalgoal = beagle_nf (thml,goal); 
beagle_tff finalgoal;  beagle_fof finalgoal;
write_fof "/tmp/HOLtoFOF" finalgoal;
write_tff path finalgoal;





(* Baby tests *)
val thml = [mk_thm ([],``!x:num.x >= 0``)] 
val goal :goal = ([],``2 >= 0``)
