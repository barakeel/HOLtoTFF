(* LIBRARIES *)
(* 
load "blibTactic"; open blibTactic;
load "beagle"; open beagle;
*)

(* Un problème pour METIS_TAC *)
val thml = [];
val goal: 
goal = 
([],``((x + 1 = y)  /\ (y + 1 = z)) 
       ==> (x + 2 = z)``);

metisTools.METIS_TAC thml goal;
DECIDE_TAC goal;
BEAGLE_TAC thml goal;

(* Step by step translation *)
val thml = [];
val goal : goal = ([],
``?P f. ((f = \x.x + 1) /\ (P T)) 
         ==> P (f 0 = 1)``);

val (goal1,_) = (PROBLEM_TO_GOAL_TAC thml goal);
val (goal2,_) = CNF_CONV_TAC (hd goal1);
val (goal3,_) = FUN_CONV_TAC (hd goal2);
val (goal4,_) = CNF_CONV_TAC (hd goal3);
val (goal5,_) = BOOL_CONV_TAC (hd goal4);
val (goal6,_) = CNF_CONV_TAC (hd goal5);
val (goal7,_) = NUM_CONV_TAC (hd goal6);
val (goal8,_) = CNF_CONV_TAC (hd goal7);
val (goal9,_) = (ERASE_EXISTS_TAC THEN 
                FORALL_CONJUNCTS_TAC THEN
                STRIP_CONJ_ONLY_HYP_TAC THEN
                ERASE_FORALL_TAC THEN 
                ADD_BOOL_AXIOM_TAC) (hd goal8);
val (goal10,_) = ADD_HIGHER_ORDER_TAC (hd goal9);
val (goal11,_) = 
 (ADD_FNUM_AXIOMS_TAC THEN 
  BOOL_BV_TAC THEN 
  ADD_BOOL_AXIOM_TAC) (hd goal10);

BEAGLE_TAC thml goal;

(* Set theory example *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
oal;

(* Set theory e
BEAGLE_TAC thml goal;


(* HOL4 basic example *);
show_assums := true;

(* forward proof *)
val th1 = ASSUME ``A:bool``;
val th2 = ASSUME ``B:bool``;
val th3 = CONJ th1 th2;
val th4 = DISCH ``B:bool`` th3;
val th5 = DISCH ``A:bool`` th4;
(* backward proof *)
g(`A ==> B ==> A /\ B `);
e(DISCH_TAC);
e(DISCH_TAC);
e(CONJ_TAC);
e(ACCEPT_TAC th1);
e(ACCEPT_TAC th2);

(* monomorphisation *)
  (* problem *)
val clgoal = get_cl_goal goal;
  (* details of the loop *)
val clthm = hd (clthml1);
val mclthm = filter is_monomorphable clthm;
val substll11 = map (inv match_c_cl clpb1) mclthm;
val substll21 = map (normalize_substl) substll11;
val substll31 = filter (not o null) substll11;
val substll1 = list_mult_subst substll3;
  (* loop *)
val clthml1 = map get_cl_thm thml;
map (map type_of) clthml1;
val clpb1 = (list_merge (clthml1 @ [clgoal]));
val substll1 = create_substll clthml1 clpb1;
val clthml1 = inst_cll substll1 clthml1;
  (* direct final result *)
val substll = repeat_create_substll 
                     (clthml,clgoal) 
                     (mk_list (length thml) [])
                     (mk_list (length thml) 1);
val (thml,goal) = monomorph_pb (thml,goal);

(* lambda-lifting *)
fun_conv ``P (\x y. x = f):bool``;
find_free_abs ``P (\x y. (\x.x = f))``;
fun_conv_sub  
(hd (find_free_abs ``P (\x y. (\x.x = f))``)) ``P (\x y. (\x.x = f))``;

(* bool conversion *)
bool_conv ``P (!x. P (z:bool) /\ x):bool``;

(* numeral variable *)
num_conv ``!x. ?y. x - y = 0``;

(* higher order conversion *)
app_conv "App" ``!f. f x = g x y + f y``;






