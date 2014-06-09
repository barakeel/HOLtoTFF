(* LIBRARIES *)
(* 
load "intSimps"; open intSimps;
load "Cooper"; open Cooper;
load "metisTools"; open metisTools;
show_assums := true;
load "blibMonomorph"; open blibMonomorph;
load "beagle"; open beagle;
*)

(* Running example *)
val C = new_constant ("C",``:'a -> bool``);
val D = new_constant ("D",``:'a -> int -> bool``);
val thm1 = mk_thm ([],``!(x:'a). D x (0:int)``);
val thm2 = mk_thm ([],``C = \(x:'a). D x (0:int)``);
val goal : goal = ([],``C (2:int)``);


val (thml,_) = monomorph_pb ([thm1,thm2],goal);
beagle_nf (thml,goal);

TAC_PROOF (goal, BEAGLE_TAC [thm1,thm2]);
TAC_PROOF (goal, METIS_TAC [thm1,thm2]);

(* Show TFA file *)

(* Other example *)
val P = new_constant ("P", ``:bool -> bool ``);
val goal = ([``P T``],``P ( 2+(1:int) = 3 )``);

TAC_PROOF (goal, COOPER_TAC);
TAC_PROOF (goal, METIS_TAC []);
TAC_PROOF (goal, BEAGLE_TAC []);

val easy_thm = Cooper.COOPER_PROVE ``2 + (1:int) = 3``;
TAC_PROOF (goal, (metisTools.METIS_TAC [easy_thm])) ;

SIMP_TAC int_ss [] goal;
val thm = TAC_PROOF (goal, 
            ((SIMP_TAC int_ss []) THEN (ACCEPT_TAC (ASSUME ``P T``))));

(* Show TFA file *)