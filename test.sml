(* LIBRARIES *)
(* 
load "blibBtools"; open blibBtools;
load "blibTffsyntax"; open blibTffsyntax ;
load "blibFreshvar"; open blibFreshvar;
load "blibSyntax"; open blibSyntax;
load "beaglePrintresult"; open beaglePrintresult;
load "blibReader"; open blibReader; 
load "numSyntax"; open numSyntax;
load "blibClauseset"; open blibClauseset;
load "blibExtractvar"; open blibExtractvar;
load "int_arithTheory"; open int_arithTheory;
load "beagle"; open beagle;
*)
load "Cooper"; open Cooper;
COOPER_TAC ([],``?x:num. x < 1``);

(* PROBLEM TEST *)   
beagle_tac_aux filename thml goal;

load "beagle"; open beagle;
val thml = [];
val goal : goal = ([``(x:num = 5)``],``x:num < 10``);


val thml = [];
val goal : goal = ([],``((f a b = 2) /\ (f a = g)) ==> (g b = 2)``);
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

(* suc *)
val thml = [mk_thm ([],``(x <= y) ==> (x < SUC y)``)];
val goal : goal = ([], ``(a <= b) ==> (a < SUC b)``);
(* higher order *)
val thml = [];
val goal : goal = ([],``((f a b = 2) /\ (f a = g)) ==> (g b = 2)``);
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



 
 