(* tools *)
(* 
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "tools"; open tools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "freshvar"; open freshvar;
load "extracttype"; open extracttype;
load "nametype"; open nametype;
load "namevar"; open namevar;
load "conv"; open conv; 
load "clausesettools"; open clausesettools;
load "printtff"; open printtff;
load "printtools"; open printtools;
load "printresult";open printresult;
load "higherorder"; open higherorder;
load "monomorph"; open monomorph;
load "tactic"; open tactic;
load "beagle"; open beagle;
*)

(* TEST PROBLEM *)
show_assums :=  true;
metisTools.METIS_TAC thml goal;
beagle_tac_aux filename thml goal;
fst (BEAGLE_NF_TAC thml goal);

(* test error *)


fst (ADD_FNUM_AXIOMS_TAC goal);


(* thmlist *)
val filename = "result/thmlist";
val thml = [ASSUME T] ;
val goal = ([F],F);

(* monomorphisation problem *)
val filename = "result/monomorph";
val thml = [mk_thm ([],``!x:'a y:'a. (x = y)``),
            mk_thm ([],``!x:num y:num. (x = y) ==> F``)
           ];
val goal = ([],F);
val (mthml,mgoal) = monomorph_pb (thml,goal);

(* num problem *)
(* where beagle success and metis fails *)
val filename = "result/num";
val thml = [];
val goal = ([``x=0``,``y=0``], ``f x = 0``);

(* bool problem *)
val filename = "result/bool"; 
val thml = [];
val goal : goal = ([],``P (x = x + 1) ==> P F ``);

find_free_bool (snd goal);

val goal1 = fst (PROBLEM_TO_GOAL_TAC mthml goal);
val goal2 = BEAGLE_CONV_TAC (hd goal1);
(* EXPLODE *)
val filename = "result/EXPLODE";
val thml = [] ;
val goal = 
 ([``!cs:'a . EXPLODE (IMPLODE cs:'a) = cs``,``!s:'a. IMPLODE (EXPLODE s:'a) = s``],
   ``!cs:'a . ?s:'a . cs = EXPLODE s``);
 
(* easy problem *)
val filename = "result/easypb";
val thml = [];
val goal : goal = ([],``x + 1 = x + 1``);

(* SUC *)
val filename = "result/SUC";
val thml = [mk_thm ([],``(x <= y) ==> (x < SUC y)``)];
val goal : goal = ([], ``(a <= b) ==> (a < SUC b)``);

(* a bit harder *)
val filename = "result/easypb2";   
val thml = [];
val goal : goal = ([],``((x + 1 = y)  /\ (y + 1 = z)) ==> (x + 2 = z)``);

(* test higher order *)
val filename = "result/higherorder";   
val thml = [];
val goal : goal = ([],``((f a b = 2) /\ (f a = g)) ==> (g b = 2)``);

(* test boolarg *)
val filename = "result/boolarg"; 
val thml = [];
val goal : goal = ([],``P (!x. x = 0) ==> P F ``);

(* test funconv *)
val filename = "result/funconv";   
val thml = [];
val goal : goal = ([],``(!y:num -> num . P y) ==> (P (\x. x + 5))`` );





(* interesting error


*)
 
 
(* dictionnary test 
val term = list_mk_conj (fst (goal) @ [snd goal]);
val fvdict = create_fvdict term;
val bvdict = create_bvdict term;
val cdict = create_cdict term;
*)      

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
pptff_term conclt;

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


val SZSstatus = "test";
val goal : goal = ([],``x + 1 = x + 1``);
val path = "/home/thibault/Desktop/SMLproject/HOLtoTFF/result/test";
write_result path goal SZSstatus;
(* use of beagle tac *)
val thml = [];
BEAGLE_TAC thml goal; 

(snd it) [];
mk_neg `` ¬(x:bool)``;
(* examples *)
val goal = ([``x = 0``,``y = 0``], F); 


bool_conv ``P (!x. x = 0):bool``;