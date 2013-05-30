
val mysmlpath = "/home/thibault/Desktop/SMLfile/HOLtoTFF/tools/"; (*not very portable*)
(*load tools*)

open stringtools;
open listtools;
open mydatatype;
open extracttype;
open extractterm;
open name;

open printtff;

(* testproblem *)
show_assums := true;
val hyp1 = ``!x:num.  x + f x = x``;
val hyp2 = ``(2,3) = y``;
val hyp3 = ``(f a = f b) /\ (a 2 = 2)``;
val hyp4 = ``?x. P x``;
val hyp5 = ``!x. (P x ==> Q x)``;

val goal = ``!x:num. f x = 0``;
val goal2 = ``!x. Q x``; 

val thm = mk_thm ([hyp4,hyp5],goal2);
outputtff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;
(* end testproblem *)

(* testfunctions *)
namefvcl [hyp1,hyp2,hyp2,goal];
open HolKernel;
is_minus ``5:int-6:int``;
pairSyntax
open folTools;
FOL_NORM ([mk_thm([``(y,x) = (2,3)``],`` (\x .(\y.y)) f 5 = 0 ``)]);
open intSyntax;
type_of ``~1``;
open pairSyntax

fun NAME_ERR function message =
  HOL_ERR{origin_structure = "name",
          origin_function = function,
          message = message};
strip_fun ``:(num->num) -> 'a ``;  
(* end testfunctions *) 

(* ISSUES *)
(* raise an exception when there is an abstraction *)
(* don't raise an exception when applying a quantifier to a compound type term (need to)*)
(* need to transform second order type term if they are not apply to anything *)
(* don't manage pairSyntax *)
(* don't manage intSyntax *)
(* manage a part of numSyntax *)
(* ~ can be seen as as neg or intneg *)
(* should translate at least -a from the intSyntax*)
(* can a type be named with an underscore in hol? in this case name should be numbered*)
(* take a function in argument is not possible *)

(* IDEA *)
(* define a newtype pair_num_num for num # (num->num) *)
(* rename Apptype if they are not apply to anything *)
(* rename Prodtype num # num *)
(* FOL_NORM deals with abstraction *)
(* it does beta-eta reduction first *)

(* CODE QUESTIONS *)
(* use of svn for my file? share with Keller Chantal*)
(* how to open emacs faster *)
(* how to kill hol faster or *)
(* how to reconstruct all my file when changing directory Holmake *)
