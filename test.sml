(* LIBRARIES *)
(* 
load "blibTools"; open blibTools;
load "blibExtract"; open blibExtract;
load "blibName"; open blibName;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibPrinter"; open blibPrinter;
load "beagle"; open beagle;
load "intSyntax"; open intSyntax;
*)
(* load all theories *)
(** **)

(* test *)
BEAGLE_TAC thml goal;


val finalgoal = beagle_nf (thml,goal); 
beagle_tff finalgoal;  beagle_fof finalgoal;
write_fof "/tmp/HOLtoFOF" finalgoal;
write_tff path finalgoal;

filter is_linarith_thm thm = (inv mem) get_cl_thm 
  [term
  val one_tm         : term
  val negate_tm      : term
  val absval_tm      : term
  val plus_tm        : term
  val minus_tm       : term
  val mult_tm        : term


fun is_arith_term = figet_cl_term 

fun is_arithmetic_thm = get_cl_thm 


DB.match p 


(* Baby tests *)
val thml = [mk_thm ([],``!x:num.x >= 0``)] 

