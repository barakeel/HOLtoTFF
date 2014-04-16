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
val ALT_SIMPLIFY_CONV = SIMP_CONV (simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss)) [];
(* test on arithmetics theory *)
load "blibExtract"; open blibExtract;
fun is_arith_thm thm = 
  null (get_cl_thm (CONV_RULE ALT_SIMPLIFY_CONV thm))
  
val athml = map (fst o snd) (DB.matchp is_arith_thm ["int_arith","integer"]);
load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC []))) (map dest_thm athml);

(* test on every theory *)
load "blibExtract"; open blibExtract;

load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC []))) (map dest_thm thml);
List.length badthml;

BEAGLE_TAC [] (dest_thm (List.nth (thml,13)));
val thml = List.nth (thml,13);
val (thml,goal) =  ([]:thm list,(dest_thm thm));
beagle_nf ([],(dest_thm thm));
beagle_nf ([], ([],`∀f g. (∀x. f x = g x) ⇒ (f = g)``));
(* test *)
val goal : goal = ([], ``∀x. 0 ≤ x + x ⇔ 0 ≤ x``)          
val goal : goal = ([],``∀f g. (∀x. f x = g x) ⇒ (f = g)``) 


val goal : goal = ([], ``(!x. (P(x:bool) = F)) ==> (P(y) = F)``);
beagle_nf ([], goal);
BEAGLE_TAC [] goal;