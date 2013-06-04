(* holpath /Desktop/SMLfile/HOLtoTFF *)

(*load tools*)
open stringtools;
open listtools;
open mydatatype;
open extracttype;
open extractvar;
open name;
open higherorder;
open printtff;

(* testproblem *)
show_assums := true;
val hyp1 = ``!x:num.  x + f x = x``;
val hyp2 = ``(2,3) = y``;
val hyp3 = ``(f a = f b) /\ (a x = x)``; (* higher order test + number test *)

val hyp4 = ``?x. P x``;
val hyp5 = ``!x. (P x ==> Q x)``;

val hyp6 = ``!f:num->num. f = g``;  (* false higher order test *)
val hyp7 = ``g = h:num->num ``;
val goal3 = ``!f:num->num. f = h``;


val goal = ``!x:num. f x = 0``;
val goal2 = ``!x. Q x``; 



val thm = mk_thm ([hyp6,hyp7],goal3);
outputtff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;
(* end testproblem *)
cd Desktop/eclipsefile/beagleproject
./beagle problem.p

(* testfunctions *)
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
FOL_NORM ([mk_thm([``(y,x) = (2,3)``],`` (\x .(\y.y)) f 5 = 0 ``)]);
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
(* all types should be alphanumor_ for now *)
(* don't manage ?! *)
(* clash between names of variables and name for types because types are variables of ttype in tff *)


(* IDEA *)
(* define a newtype pair_num_num for num # (num->num) *)
(* rename Apptype if they are not apply to anything *)
(* rename Prodtype num # num *)
(* FOL_NORM deals with abstraction *)
(* it does beta-eta reduction first *)
(* use dest_var dest_thy_const *)
(* replace the use of dest_const by dest_thy_const to add the axioms of the theory pair is i (case by case analysis maybe better) *)
(* get rid of alphanm everywhere if possible *)
(* name the variables starting by a "x" constant by starting with "c" *)

(* CODE QUESTIONS *)
(* how to open emacs faster *)


