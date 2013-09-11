(* LIBRARIES *)
(* 
load "beagle"; open beagle;
*)

(* PROBLEM TEST *)   
beagle_tac_aux filename thml goal;
BEAGLE_TAC thml goal;
fst (BEAGLE_NF_TAC thml goal);

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
val thml = [mk_thm ([],``1+1 = 2``)];
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

(* PAPER EXAMPLES *)


 
 