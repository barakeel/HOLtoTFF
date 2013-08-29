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

(* monomorphisation *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);


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
val filename = "result/monomorph2";
val th1 = mk_thm ([],``!x. x = y ``);
val thml = [th1];
val goal:goal = ([], ``2 = 3``);
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
val clthml = map get_cl_thm thml;
val clgoal = get_cl_goal goal;
val substll = create_substll(clthml,clgoal);
val newclthml = inst_cll substll clthml;
val newclpb = (newclthml,clgoal);
val newsubstll = create_substll newclpb;
val instnl = map length substll;
val newinstnl = map length newsubstll;
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
val term = ``x ∈ X = ∃i. LNTH i (LUNFOLD f lo) = SOME x``;
val term = 
``∀r s. finite_prefixes r s = ∀e. e ∈ s ==> FINITE {e' | (e',e) ∈ r}``;

val term = 
``∀s.
     FINITE s ==>
     ∀lo X x.
       x ∈ X /\ (s = {y | (y,x) ∈ lo}) /\ linear_order lo X /\
       finite_prefixes lo X ==>
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x``;

(normalForms.CNF_CONV THENC fun_conv THENC normalForms.CNF_CONV
THENC bool_conv) term;



val th1 = mk_thm ([],`` ∀x y. (SOME x = SOME y) = (x = y)``)
val th2 = mk_thm ([],`` 
   (∀n. LNTH n [||] = NONE) /\ 
   (∀h t. LNTH 0 (h:::t) = SOME h) /\
   ∀n h t. LNTH (SUC n) (h:::t) = LNTH n t ``);

val thml = [th1,th2];
val thml = [];

val goal : goal = ([],``
   ∀x.
      let n = LEAST n. ∃e. (SOME e = LNTH n x) /\ P e
         in
           (THE (LDROP n x)) P a = y ``);
 
 val goal : goal = ([],``SOME (THE (LDROP (SUC n) x),THE (LNTH n x))``);