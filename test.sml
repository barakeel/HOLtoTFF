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

(* PROBLEM TEST *)
show_assums :=  true;
metisTools.METIS_TAC thml goal;
beagle_tac_aux filename thml goal;
fst (BEAGLE_NF_TAC thml goal);

(* NLIA test *)
val filename = "result/nlia";
val thml = [] ;
val goal = ([``(x * y = 4)``],``(y * x = 4)``);

(* test error *)
val filename = "result/abstraction";
val thml = [] ;
val goal : goal = ([],
`` P (λll. (let n = LEAST n. ∃e. (e = 0) in ll)) : bool ``
);
(* nlia *)
val filename = "result/nlia";
val thml = [mk_thm ([],``!x. ( (x * x) = 4) ==> (x=2)``)] ;
val goal = ([``(x * x = 4)``],``(x=2)``);

(* thmlist *)
val filename = "result/thmlist";
val thml = [ASSUME T] ;
val goal = ([F],F);

(* monomorphisation problem *)
val filename = "result/monomorph1";
val thml = [mk_thm ([],``!x:'a y:'a. (x = y)``),
            mk_thm ([],``!x:num y:num. (x = y) ==> F``)
           ];
val goal = ([],F);
val (mthml,mgoal) = monomorph_pb (thml,goal);

val filename = "result/monomorph2";
val thml = [mk_thm ([],``((x:num = z:num) = y:bool)``)];
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

(* a bit harder *)
val filename = "result/easypb2";   
val thml = [];
val goal : goal = ([],``((x + 1 = y)  /\ (y + 1 = z)) ==> (x + 2 = z)``);

(* SUC *)
val filename = "result/SUC";
val thml = [mk_thm ([],``(x <= y) ==> (x < SUC y)``)];
val goal : goal = ([], ``(a <= b) ==> (a < SUC b)``);

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
val goal : goal = ([],``(!y:num -> num -> num . P y) ==> (P (\x y. x + y))`` );

(* DICITIONNARY TEST *)      
val term = list_mk_conj (fst (goal) @ [snd goal]);
val fvdict = create_fvdict term;
val bvdict = create_bvdict term;
val cdict = create_cdict term;
val tyadict = create_tyadict term;

