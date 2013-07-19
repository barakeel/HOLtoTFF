(* tools *)
(* 
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "tools"; open tools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
load "nametype"; open nametype;
load "namevar"; open namevar;
load "conv"; open conv; 
load "rule"; open rule; 
load "printtff"; open printtff;
load "printresult";open printresult;
load "higherorder"; open higherorder;
load "beagle"; open beagle;
*)

(* TEST PROBLEM *)
show_assums :=  true ;


(* use of beagle tac *)
val thml = [];
BEAGLE_TAC thml goal; 
metisTools.METIS_TAC thml goal;
(snd it) [];

(* test higher order *)
val goal : goal = ([],``(f a b = 2) /\ (f a = g)``);
val filename = "result/higherorder";   
val thml = [];
val prepareflag = true;
val monomorphflag = false;
beagle filename thml goal prepareflag monomorphflag; 

(* test boolarg *)
val goal : goal = ([],``P (!x. x = 0) ==> P F ``);
val filename = "result/boolarg";   
val thml = [];
val prepareflag = true;
val monomorphflag = false;
beagle filename thml goal prepareflag monomorphflag; 




(* problem 1 *)
val goal : goal = ([],``(x = 1) ==> (x = 1)``);
val filename = "result/test1";   
val thml = [];
val prepareflag = true;
val monomorphflag = false;
beagle filename thml goal prepareflag monomorphflag; 

(* problem 2 *)
val goal : goal = ([],``(!x. x + x = 1) ==> (x = 1)``);
val filename = "result/problem2";   
val thml = [];
val prepareflag = false;
beagle filename thml goal prepareflag; 

(* problem 3 *)
val goal : goal = ([],``(x + x = 1) ==> (x = 1)``);
val filename = "result/problem3";   
val thml = [];
val prepareflag = false;
beagle filename thml goal prepareflag; 

(* problem 4 *)
val goal : goal = ([],``(x + x = 1) ==> (x = 1)``);
val filename = "result/problem4";   
val thml = [];
val prepareflag = false;
beagle filename thml goal prepareflag; 


(* test functions *)
open HolKernel Abbrev boolLib;
is_minus ``5:int-6:int``;
pairSyntax

open folTools;
FOL_NORM ([mk_thm([],``!x. (!x. x = 0) /\ (x = 0) ``)]); 
FOL_NORM ([ASSUME ``(\x.x) = (\z.w) ``]);

e(FOL_NORM_TAC);
drop;
(* failure *)
FOL_NORM ([mk_thm([],``(\z.x) = (\y.y)``)]); (* mk_thm *)

open Hol_pp;
print_term conclt;

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

(* Rewriting ... Normalizing *)
val term2 = rand (concl (REDEPTH_CONV BETA_CONV term));  (* to be rewritten *)
  (* may raise unchanged *)
val term3 = rand (concl (REDEPTH_CONV ETA_CONV term2)); (* may raise QConv.UNCHANGED *)
  (* skolemisation *) 
val term4 = rand (concl (REDEPTH_CONV SKOLEM_CONV term2));

(* END TEST FUNCTIONS *) 
