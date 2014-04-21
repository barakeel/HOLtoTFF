(* LIBRARIES *)
(* 
load "blibTools"; open blibTools;
load "blibName"; open blibName;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibPrinter"; open blibPrinter;
load "beagle"; open beagle;
load "intSyntax"; open intSyntax;
*)
(* some necessary extensionality theorems *)
val thm1 = INST_TYPE [alpha |-> ``:int``, beta |-> ``:int``] EQ_EXT;
val thm2 = INST_TYPE [alpha |-> bool, beta |-> bool] EQ_EXT;

val ALT_SIMPLIFY_CONV = SIMP_CONV (simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss)) [];
load "blibExtract"; open blibExtract;
fun is_arith_thm thm = null (get_cl_thm (CONV_RULE ALT_SIMPLIFY_CONV thm));

val thml =  map (fst o snd) (DB.matchp is_arith_thm ["bool"]);
load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC [EQ_EXT,thm1,thm2]))) (map dest_thm thml);
List.length badthml;

val thm = dest_thm (List.nth (thml,12));
BEAGLE_TAC [EQ_EXT,thm1,thm2] thm;
(* add necessary theorems *)
(* instantiation of extensionality *)
success BEAGLE_TAC [thm2] (dest_thm (BOOL_FUN_CASES_THM));
val thml = List.nth (thml,13);
val (thml,goal) =  ([]:thm list,(dest_thm thm));
beagle_nf ([],(dest_thm thm));
beagle_nf ([], ([],));
(* test *)

beagle_nf ([], goal);