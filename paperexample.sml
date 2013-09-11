(* LIBRARIES *)
(* 
load "basictools"; open basictools;
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "mydatatype"; open mydatatype;

load "syntax"; open syntax;
load "tffsyntax"; open tffsyntax;
load "tffBconv"; open tffBconv;
load "basicrule"; open basicrule;
load "predicate"; open predicate;
load "extractterm"; open extractterm;
load "extractvar"; open extractvar;
load "blibFreshvar"; open blibFreshvar;
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


(* arithmetic for substitution *)
add_subst [``:'a`` |-> ``:bool``] [``:'b`` |-> ``:bool``]; 
mult_subst 
  [[``:'a`` |-> ``:bool``], [``:'b`` |-> ``:bool``]]
  [[``:'b`` |-> ``:num``] , [``:'c`` |-> ``:num``]];
get_maxsubstl it;

(* monomorphisation *)
  (* problem *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
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
                     (make_list_n (length thml) [])
                     (make_list_n (length thml) 1);
val (thml,goal) = monomorph_pb (thml,goal);




