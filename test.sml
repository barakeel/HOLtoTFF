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

(* PAPER EXAMPLES *)
(* arithmetic for substitution *)
add_subst [``:'a`` |-> ``:bool``] [``:'b`` |-> ``:bool``]; 

mult_subst 
  [[``:'a`` |-> ``:bool``], [``:'b`` |-> ``:bool``]]
  [[``:'b`` |-> ``:num``] , [``:'c`` |-> ``:num``]];
  
get_maxsubstl it;




(* PROBLEM TEST *)   
show_assums :=  true;
metisTools.METIS_TAC thml goal;
beagle_tac_aux filename thml goal;
fst (BEAGLE_NF_TAC thml goal);
val (thml,goal) = monomorph_pb (thml,goal);

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
val filename = "result/monomorph";
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
(* num *)
val filename = "result/num";
val thml = [];
val goal = ([``x=0``,``y=0``], ``f x = 0``);
(* bool *)
val filename = "result/bool"; 
val thml = [];
val goal : goal = ([]val th1 = mk_thm ([],
`` ∀s.
     FINITE s ⇒
     ∀lo X x.
       x ∈ X ∧ (s = {y | (y,x) ∈ lo}) ∧ linear_order lo X ∧
       finite_prefixes lo X ⇒
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x ``);
val th2 = mk_thm ([], 
``∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}``);
val thml = [];,``P (x = x + 1) ==> P F ``); 
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
val goal : goal = ([]val th1 = mk_thm ([],
`` ∀s.
     FINITE s ⇒
     ∀lo X x.
       x ∈ X ∧ (s = {y | (y,x) ∈ lo}) ∧ linear_order lo X ∧
       finite_prefixes lo X ⇒
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x ``);
val th2 = mk_thm ([], 
``∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}``);
val thml = [];,``P (!x. x = 0) ==> P F ``);
(* funconv *)
val filename = "result/funconv";   
val thml = [];
val goal : goal = ([],``(!y:num -> num -> num . P y) ==> (P (\x y. x + y))`` );

(* DEBUGGING *)
(* bool conv *)
bool_conv term;
bool_conv ``P (!x. P (z /\ T) /\ x):bool``;
bool_conv ``P (b:bool) :bool``;
bool_conv ``P (!x. P (b:bool))``;
(* top down approach *)
bool_conv ``P ( P ( b:bool)):bool``;
bool_conv_sub_one ``P ( P ( b:bool)):bool``;
bool_conv_sub_one ``P (b:bool) :bool``;
bool_conv_sub_all ``P ( P ( b:bool)):bool``;

(* monomorphisation *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
val clgoal = get_cl_goal goal;

val clthml1 = map get_cl_thm thml;
map (map type_of) clthml1;
val clpb1 = (list_merge (clthml1 @ [clgoal]));
val substll1 = create_substll clthml1 clpb1;

val clthm = hd (clthml1);
val mclthm = filter is_monomorphable clthm;
val substll11 = map (inv match_c_cl clpb1) mclthm;
val substll21 = map (normalize_substl) substll11;
val substll31 = filter (not o null) substll11;
val substll1 = list_mult_subst substll3;

val clthml2 = inst_cll substll1 clthml1;
map (map type_of) clthml2;
val clpb2 = (list_merge (clthml2 @ [clgoal]));
val substll2 = create_substll clthml2 clpb2;

val clthml3 = inst_cll substll2 clthml2;
map (map type_of) clthml3;
val clpb3 = (list_merge (clthml3 @ [clgoal]));
val substll3 = create_substll clthml3 clpb3;

val substll = repeat_create_substll 
                     (clthml,clgoal) 
                     (make_list_n (length thml) [])
                     (make_list_n (length thml) 1);
val (thml,goal) = monomorph_pb (thml,goal);

(* dictionnary *)      
val term = list_mk_conj (fst (goal) @ [snd goal]);
val fvdict = create_fvdict term;
val bvdict = create_bvdict term;
val cdict = create_cdict term;
val tyadict = create_tyadict term;

(* ERROR *)
val th1 = mk_thm ([],
`` ∀s.
     FINITE s ⇒
     ∀lo X x.
       x ∈ X ∧ (s = {y | (y,x) ∈ lo}) ∧ linear_order lo X ∧
       finite_prefixes lo X ⇒
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x ``);
val th2 = mk_thm ([], 
``∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}``);
val thml = [];
val goal = ( 
[``∀s'.
   s' ⊂ {z | (z,x) ∈ lo} ⇒
   ∀lo X x y.
     (x,y) ∈ lo ∧ (s' = {z | (z,x) ∈ lo}) ∧ linear_order lo X ∧
     finite_prefixes lo X ⇒
     ∃i j.
       i ≤ j ∧ (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x) ∧
       (LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME y) ``,``
 FINITE {z | (z,x) ∈ lo} ``,`` x ∉ X DIFF minimal_elements X lo ``,``
 minimal_elements X lo = {x'}, x ∈ X, y ∈ X, (x,y) ∈ lo ``,``
 {y | (y,x) ∈ rrestrict lo (X DIFF minimal_elements X lo)} ⊂
 {y | (y,x) ∈ lo}, X DIFF minimal_elements X lo ⊆ X ``,``
 finite_prefixes lo X ``,``
 finite_prefixes (rrestrict lo (X DIFF minimal_elements X lo))
   (X DIFF minimal_elements X lo) ``,`` linear_order lo X ``,``
 linear_order (rrestrict lo (X DIFF minimal_elements X lo))
   (X DIFF minimal_elements X lo)``]
, ``∃j. LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME y``);

BEAGLE_NF_TAC

val term = 
``∀s'.
   s' ⊂ {z | (z,x) ∈ lo} ⇒
   ∀lo X x y.
     (x,y) ∈ lo ∧ (s' = {z | (z,x) ∈ lo}) ∧ linear_order lo X ∧
     finite_prefixes lo X ⇒
     ∃i j.
       i ≤ j ∧ (LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x) ∧
       (LNTH j (LUNFOLD linear_order_to_list_f lo) = SOME y)``;

val term = ``∀s.
     FINITE s ⇒
     ∀lo X x.
       x ∈ X ∧ (s = {y | (y,x) ∈ lo}) ∧ linear_order lo X ∧
       finite_prefixes lo X ⇒
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x``;

val term = ``∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}``;

val term = ``


(normalForms.CNF_CONV THENC fun_conv THENC normalForms.CNF_CONV
THENC bool_conv) term;

 
 
 
 
 
 
 