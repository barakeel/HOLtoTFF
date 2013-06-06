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

val thm = mk_thm ([hyp10,hyp11],goal4); (* mk_thm may not work  as expected *)
outputtff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;
(* end testproblem *)
(* cd Desktop/eclipsefile/beagleproject *)
(*  *)



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
airSyntax
open folTools;
FOL_NORM ([mk_thm([],``!x. (!x. x = 0) /\ (x = 0) ``)]); (* rename bound variable *)
FOL_NORM ([mk_thm([],``(\z.x) = (\y.y) ``)]);
FOL_NORM ([mk_thm([],``(\x.x) = (\z.w) ``)]);
FOL_NORM ([ASSUME ``(\x.x) = (\z.w) ``]);
FOL_NORM ([ASSUME goal3]);
folTools.pp_logic_map;
folTools.build_map
set_goal([],goal3);
e(FOL_NORM_TAC);
drop;
open Hol_pp;
print_term goal;

open intSyntax;
type_of ``~1``;
open pairSyntax

fun NAME_ERR function message =
  HOL_ERR{origin_structure = "name",
          origin_function = function,
          message = message};
strip_fun ``:(num->num) -> 'a ``;  

dest_type ``:num``;
numSyntax.int_of_term ``-521``;
(* END TESTFUNCTIONS *) 

(* ISSUES *)

(* types  *)
  (* already defined type appears in the list of declared type *)
  (* clash occurs between names *)
  (* declare predefined types *)
  (* doesn't declare type for bound variables *)
  (* sometimes declare twice a type *)
(* betaeta - red *) 
  (* raise an exception when there is an abstraction *)
(* higher order *)
  (* raise a exception when encountering higher order *)
(* pretty printing *)
  (* no break *)
(* functionnality *)
  (* pairSyntax *)
  (* intSyntax *)
  (* numSyntax *)
  (* boolSyntax *)
    (* argument can not be of $otype maybe need to rewrite boolean *)
    (* equality as boolean equality *)
    (* ~ can be seen as as neg or intneg *)
    (* don't manage ?! , = as equivalence *)


(* IDEA *)

(* use dest_var dest_thy_const *)
(* replace the use of dest_const by dest_thy_const to add the axioms of the theory pair*)
(* get rid of alphanm everywhere if possible *)
(* name the variables starting by a "x" constant by starting with "c" *)


(* CODE QUESTIONS *)
(* some code keep appearing in my text editor when I am doing alt+ h then 
 alt + h alt + r *)
(* how to open emacs faster *)


(* TODO *)

(* beta-eta reduction *) (* lambda-abstraction *)
  (* skolemisation *)
(* second order *)
(* definition for fvc,type *)
  (* add important theorem *) (* my appreciation *)
  (* add all the theory *)
