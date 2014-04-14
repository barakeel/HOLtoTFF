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

(* test on arithmetics theory *)
load "blibExtract"; open blibExtract;
fun is_arith_thm thm = 
  let val l = (get_cl_thm thm) in
    null l orelse ((length l = 1) andalso fst (dest_const (hd l)) = "COND")
  end
  handle _ => false
  
val athml = map (fst o snd) (DB.matchp is_arith_thm ["int_arith","integer"]);
load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC []))) (map dest_thm athml);

(* test on every theory *)
load "blibExtract"; open blibExtract;
fun is_arith_thm thm = 
  let val l = (get_cl_thm thm) in
    null l orelse ((length l = 1) andalso fst (dest_const (hd l)) = "COND")
  end
  handle _ => false
val thml = map (fst o snd) (DB.matchp is_arith_thm []);
val thm = hd thml;

load "blibTools"; open blibTools;
val badthml = filter (not o (success (BEAGLE_TAC []))) (map dest_thm thml);

BEAGLE_TAC [] (dest_thm (List.nth (thml,8)));


val thml = List.nth (thml,13);
val (thml,goal) =  ([]:thm list,(dest_thm thm));
beagle_nf ([],(dest_thm thm));

(* test *)