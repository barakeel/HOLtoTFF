(* LIBRARIES *)
(* 
load "blibBtools"; open blibBtools;
load "blibTffsyntax"; open blibTffsyntax ;
load "blibFreshvar"; open blibFreshvar;
load "blibSyntax"; open blibSyntax;

load "numSyntax"; open numSyntax;
load "intSyntax"; open intSyntax;

load "blibExtractvar"; open blibExtractvar;
load "int_arithTheory"; open int_arithTheory;
load "blibBtactic"; open blibBtactic;
load "blibTactic"; open blibTactic;
load "blibNumconv"; open blibNumconv;

load "blibReader"; open blibReader;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;

load "beagle"; open beagle;
*)
show_assums := true;


(snd (Cooper.COOPER_TAC goal)) [];
(snd (metisTools.METIS_TAC [] goal)) [];
BEAGLE_NF_TAC thml goal;
BEAGLE_PROVE thml goal;
PROVE_SIMP goal;

val thml = [];
val goal : goal = ([``A ==> B``, ``B ==> C``], ``A ==> C``);
val goal : goal = ([``(x:int = 1) ==> (y:int = 2)``, ``(y:int = 2) ==> (z:int = 3)``], 
``(x:int = 1) ==> (z:int = 3) ``);


val goal : goal = ([``¬((y:int) ≠ x)``,``(x:int) + (-(y:int)) ≠ 0``], F);
val goal : goal = ([],``((f a b = 2:int) /\ (f a = g)) ==> (g b = 2:int)``);
val goal : goal = ([``!f. f (0:int) (x:num) = 2:int``],F);
val goal : goal = ([``!f. f (0:int) = 2:int``],F);
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``],F);
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``,
                  ``not (0:int = 2)``],F);

val th1 = mk_thm ([], ``∀n. (s2n :int -> int) (n2s n) = n``);
val thml = [th1];
val goal:goal = ([], ``((n2s :int -> int) x = n2s y) ⇔ (x = y)``);

val th1 = mk_thm ([], ``∀n. (s2n :'a -> 'a) (n2s n) = n``);
val thml = [th1];
val goal:goal = ([], ``((n2s :'a -> 'a) x = n2s y) ⇔ (x = y)``);

val th1 = mk_thm ([], ``∀n. (s2n :num -> num) (n2s n) = n``);
val thml = [th1];
val goal:goal = ([], ``((n2s :num -> num) x = n2s y) ⇔ (x = y)``);


(* problem 1 *)
val th1 = mk_thm ([],``∀P l. LENGTH (SND (SPLITP P l)) ≤ LENGTH l``);
val th2 = mk_thm ([],``(a:num) ≤ b ⇒ (a:num) < (SUC:num->num) b``);
val thml = [th1,th2];
val goal = ([``¬P h``],``LENGTH (SND (SPLITP P t)) < (SUC:num->num) (LENGTH t)``);

val th1 = mk_thm ([],``∀P l. LENGTH (SND (SPLITP P l)) ≤ LENGTH l``);
val th2 = mk_thm ([],``a ≤ b ⇒ (a:num) < SUC b``);
val thml = [th1,th2];
val goal = 
([``¬(P:'a -> bool) (h:'a)``],
``(LENGTH:'a list-> num) 
  ((SND: 'a list # 'a list -> 'a list) 
  (SPLITP (P:'a -> bool) (t:'a list))) < 
  (SUC:num->num) ((LENGTH :'a list-> num) t)``);

val th1 = mk_thm ([], ``∀m:num n. m * n = n * m ``);
val th2 = mk_thm ([], ``∀n:num q. 0 < n ⇒ (q * n DIV n = q) ``);
val th3 = mk_thm ([], ``0:num < 256``);

val thml = [th1,th2,th3];
val goal =
([``Abbrev (s0 = n2s (256:num * s2n s DIV 256)) :bool``, ``r0 ≠ 0:num``, 
  ``ORD c + 1 < (256:num) ``,
 ``n2s (s2n s) = s``, ``r0 = ORD c + 1:num``] , ``s0 = s``);
 


BEAGLE_TAC thml goal;
BEAGLE_NF_TAC thml goal;




val (mthml,_) = monomorph_pb (thml,goal);
val (finalgoall,valid) = BEAGLE_NF_TAC mthml goal;
is_correct_tac1 goal (finalgoall,valid);
val th1 = mk_thm (hd finalgoall);
val th2 = valid [th1];
mk_thm (hd finalgoall);

val (goal1,_) = PROBLEM_TO_GOAL_TAC mthml goal;
val (goal2,_) = BEAGLE_CONV_TAC (hd goal1);
val (goal3,_) = ERASE_EXISTS> _TAC (hd goal2);
val (goal4,_) = FORALL_CONJUNCTS_TAC (hd goal3);
val (goal6,_) = STRIP_CONJ_ONLY_HYP_TAC (hd goal4); 
val (goal7,_) = ERASE_FORALL_TAC (hd goal6);
val (goal8,_) = ADD_HIGHER_ORDER_TAC (hd goal7);
val (goal9,_) = NUM_INT_TAC (hd goal8);
val (goal10,_) = BOOL_BV_TAC (hd goal9);
val (goal11,_) = ADD_BOOL_AXIOM_TAC (hd goal10);

(* debugging *)
val thml = [mk_thm ([], ``∀l x. MEM x l ⇔ ∃n. n < LENGTH l ∧ (x = EL n l)``)];
val goal = ([``Abbrev (m1 = LENGTH (FILTER ($= x) l1))``,
            ``Abbrev (m2 = LENGTH (FILTER ($= x) l2))``],
 ``MEM (EL x' (FILTER ($= x) l1)) (FILTER ($= x) l1) ∧
   MEM (EL x' (FILTER ($= x) l2)) (FILTER ($= x) l2)``);

BEAGLE_TAC thml goal;


(* PROBLEM TEST *)   
val thml = [];
val goal : goal = ([``(x:num = 5) /\ (y:num = 2)``],``x:num = 5``);
BEAGLE_TAC thml goal;

val thml = [];
val goal : goal = ([],``((f a b = 2:int) /\ (f a = g)) ==> (g b = 2:int)``);
BEAGLE_TAC thml goal;


(* nlia test *)
val thml = [] ;
val goal = ([``(x * y = 4)``],``(y * x = 4)``);
(* abstraction *)
val thml = [] ;
val goal : goal = ([],
                   `` P (λll. (let n = LEAST n. ∃e. (e = 0) in ll)) : bool ``);
                   
                  
(* monomorphisation *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
(* num *)
val thml = [];
val goal = ([``x=0``,``y=0``], ``f x = 0``);
(* bool *)
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
val thml = [];
val goal : goal = ([],``x + 1 = x + 1``);

val thml = [];
val goal = ([``(f x = 4:num)``], F );


(* suc *)
val thml = [mk_thm ([],``(x <= y) ==> (x < SUC y)``)];
val goal : goal = ([], ``(a <= b) ==> (a < SUC b)``);
(* higher order *)
val thml = [];
val goal : goal = ([],``((f a b = 2:int) /\ (f a = g)) ==> (g b = 2:int)``);
(* boolarg *)
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
val thml = [];
val goal : goal = ([],``(!y:num -> num -> num . P y) ==> (P (\x y. x + y))`` );



 
 