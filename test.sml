(*load tools*)
open stringtools;
open listtools;
open mydatatype;
open extractvar;
open extracttype;
open name;
open higherorder;
open printtff;

(* testproblem *)
show_assums := true;
val hyp1 = ``!x:num.  x + f x = x``;
val hyp2 = ``(2,3) = y``; (* couple test *)
val hyp3 = ``(f a = f b) /\ (a x = x)``; (* higher order test + number test *)
val hyp4 = ``?x. P x``;
val hyp5 = ``!x. (P x ==> Q x)``;
val hyp6 = ``!f:num->num. f = g``;  (* false higher order test *)
val hyp7 = ``g = h:num->num ``;
val hyp8 = ``!x.?y.!z. x + y = z``; (* pretty printing *)
val hyp9 = ``(\x.x) 5 = 5``; (* simplest abstraction *)

(* shouldn't work in beagle *)
val hyp10 =  ``f (x:bool) = (~x)``;
val hyp11 =  `` x = F ``;
val goal4 = ``f x = T ``;

val goal = ``!x:num. f x = 0``;
val goal2 = ``!x. Q x``; 
val goal3 = ``!f:num->num. f x = 0``;
val goalfalse = ``F``;

val thm = mk_thm ([hyp4],hyp4); (* mk_thm may not work  as expected *)
outputtff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;

(* end testproblem *)
(* cd Desktop/eclipsefile/beagleproject *)
(*  *)
(* failure *)
val thm = mk_thm ([hyp4],hyp4); (* pp (now works but if you add begin block at quantifier then it doesn't work) *)
folTools.FOL_NORM ([mk_thm([],``(\z.x) = (\y.y)``)]); (* mk_thm *)

(* TESTFUNCTIONS *)
val hypl = hyp thm;
val propl = hypl @ [concl thm]; 
val varl = extractvarl propl; 
val fvcdcl = erasedouble (erasenumber (erasebv varl));
strip_forall hyp6;
free_varsl propl;
namefvcl [hyp1,hyp2,hyp2,goal]; 

open HolKernel;
is_minus ``5:int-6:int``;
pairSyntax

open folTools;
FOL_NORM ([mk_thm([],``!x. (!x. x = 0) /\ (x = 0) ``)]); (* rename bound variable *)
FOL_NORM ([ASSUME ``(\x.x) = (\z.w) ``]);
set_goal([],goal3);
e(FOL_NORM_TAC);
drop;

open Hol_pp;
print_term goal;

open intSyntax;
type_of ``~1``;

open pairSyntax
strip_fun ``:(num->num) -> 'a ``;  
dest_type ``:num``;
numSyntax.int_of_term ``-521``;

open mlibTerm;
open mlibTptp;
read {filename = "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p"};
val formula = False;
write {filename = "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p"} formula;

(* betared *)
val term = `` ((\x.x) 0 = 0) /\ (\y.M y) x`` ;
val term = ``(\x.x) \x. f x ``;

val term2 = rand (concl (REDEPTH_CONV BETA_CONV term));  (* to be rewritten *)
(* may raise unchanged *)
val term3 = rand (concl (REDEPTH_CONV ETA_CONV term2)); (* may raise QConv.UNCHANGED *)

val SKOLEM_CONV

(* skolemisation *) 






(* END TESTFUNCTIONS *) 

(* ISSUES *)

(* types  *)
  (* clash occurs between names * )
(* betaeta - red *) 
  (* raise an exception when there is an abstraction *)
(* higher order *)
  (* raise a exception when encountering higher order *)
(* pretty printing *)
  (* don't understand how it works *)
(* functionnality *)
  (* pairSyntax *)
  (* intSyntax *)
  (* numSyntax *)
  (* boolSyntax *)
    (* argument can not be of $otype raise an exception *)
    (* equality as boolean equality *)
    (* ~ can be seen as as neg or intneg *)
    (* don't manage ?! , = as equivalence *)


(* IDEA *)

(* use dest_var dest_thy_const *)
(* replace the use of dest_const by dest_thy_const to add the axioms of the theory pair*)
(* get rid of alphanm everywhere if possible *)



  (* CODE QUESTIONS *)
(* some code keep appearing in my text editor when I am doing alt+ h then 
 alt + h, alt + r *)
(* how to open emacs faster *)
(* is there a good editor for sml, i am currently using the text editor *)

(* TODO *)

(* modify hol formula *)
  (* beta-eta reduction *) (* lambda-abstraction *)
  (* skolemisation *)

(* after modifying holformula *)
(* modify the type *)


  (* second order *)
  (* standardize the way my code is *)



  (* definition for fvc,type *)
  (* add important theorem *) (* user appreciation maybe can defined a function that says what theorem is important *)
  (* add all the theory *)
