(* LIBRARIES *)
(* 
load "basictools"; open basictools;
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "mydatatype"; open mydatatype;

load "syntax"; open syntax;
load "tffsyntax"; open tffsyntax;
load "basicconv"; open basicconv;
load "basicrule"; open basicrule;
load "predicate"; open predicate;
load "extractterm"; open extractterm;
load "extractvar"; open extractvar;
load "freshvar"; open freshvar;
load "extracttype"; open extracttype;
load "nametype"; open nametype;
load "namevar"; open namevar;

load "monomorph"; open monomorph;
load "conv"; open conv; 
load "clausesettools"; open clausesettools;
load "tactic"; open tactic;

load "printtools"; open printtools;
load "higherorder"; open higherorder;
load "printtff"; open printtff;
load "printresult";open printresult;

load "beagle"; open beagle;
*)

(* PROBLEM TEST *)
(* main *)
show_assums :=  true;
metisTools.METIS_TAC thml goal;
beagle_tac_aux filename thml goal;
fst (BEAGLE_NF_TAC thml goal);

(* good example where monomorphing once doesn't work *)
val filename = "result/monomorph";
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);

val term = ``{y}``;
dest_comb term ;
val cl = get_cl term;
val cl1 = get_cl_thm th1;
val type1 = map type_of cl1;
val cl2 = get_cl_thm th2;
val type2 = map type_of cl2;
val clg = get_cl_goal goal;
val typeg = map type_of clg;
val (thml,goal) = (monomorph_pb (thml,goal));

(* slow down the process quite a bit *)

(* should try with 0 monomorphisation *)
(* should try with 1 - = monomorphisation *)
(* should try with 1 + = monomorphisation *)
(* should try with 2 - = monomorphisation *)


(* monomormorphisation *)
monomorph_thm_pb th1 (thml,goal);
val substl = normalize_substl (create_substl_thm_pb th1 (thml,goal));
val substl = normalize_substl (create_substl_thm_pb th2 (thml,goal));


(* dictionnary *)      
val term = list_mk_conj (fst (goal) @ [snd goal]);
val fvdict = create_fvdict term;
val bvdict = create_bvdict term;
val cdict = create_cdict term;
val tyadict = create_tyadict term;

(* EXAMPLES *)
(* nlia test *)
val filename = "result/nlia";
val thml = [] ;
val goal = ([``(x * y = 4)``],``(y * x = 4)``);
(* abstraction *)
val filename = "result/abstraction";
val thml = [] ;
val goal : goal = ([],
                   `` P (λll. (let n = LEAST n. ∃e. (e = 0) in ll)) : bool ``);
(* monomorphisation *)
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
(* num *)
val filename = "result/num";
val thml = [];
val goal = ([``x=0``,``y=0``], ``f x = 0``);
(* bool *)
val filename = "result/bool"; 
val thml = [];
val goal : goal = ([],``P (x = x + 1) ==> P F ``); 
(* easy problems *)
val filename = "result/easypb";
val thml = [];
val goal : goal = ([],``x + 1 = x + 1``);
val filename = "result/easypb2";   
val thml = [];
val goal : goal = ([],``((x + 1 = y)  /\ (y + 1 = z)) ==> (x + 2 = z)``);
(* suc *)
val filename = "result/suc";
val thml = [mk_thm ([],``(x <= y) ==> (x < SUC y)``)];
val goal : goal = ([], ``(a <= b) ==> (a < SUC b)``);
(* higher order *)
val filename = "result/higherorder";   
val thml = [];
val goal : goal = ([],``((f a b = 2) /\ (f a = g)) ==> (g b = 2)``);
(* boolarg *)
val filename = "result/boolarg"; 
val thml = [];
val goal : goal = ([],``P (!x. x = 0) ==> P F ``);
(* funconv *)
val filename = "result/funconv";   
val thml = [];
val goal : goal = ([],``(!y:num -> num -> num . P y) ==> (P (\x y. x + y))`` );



