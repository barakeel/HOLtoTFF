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
load "blibReplayer"; open blibReplayer;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;

load "beagle"; open beagle;
*)

val goal : goal = ([],``(h (x:'a) y z :bool) /\ (h (x:'a) = g)``);
BEAGLE_NF_TAC [] goal;

show_assums := true;

(* success *)
val th1 = mk_thm ([], ``∀n. (s2n :int -> int) (n2s n) = n``);
val thml = [th1];
val goal:goal = ([], ``((n2s :int -> int) x = n2s y) ⇔ (x = y)``);

val thml = [];
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``],F);

val thml = [];
val goal : goal = ([``!f. f (0:num) = 2:num``,``g (0:num) = (0:num)``],F);
BEAGLE_NF_TAC [] goal;

val thml = [];
val goal : goal = 
([],``((f a b = 3:int) /\ (f a = g)) ==> (g b = (2+1:int))``);


METIS_COOPER_CNF goal;
 val cooperthml = mk_cooperthml goal;

(snd (Cooper.COOPER_TAC goal)) [];
(snd (metisTools.FO_METIS_TAC [] goal)) [];
BEAGLE_NF_TAC thml goal;
BEAGLE_PROVE thml goal;

(* need a normalisation *)

 
fun normalise_eq term =
  let val (t1,t2) = dest_eq term in
  let val t = intSyntax.mk_minus (t1,t2) in
    mk_eq (rand (concl (OmegaMath.sum_normalise t)),``(0:int)``)
  end end
 
 fun normalise_
 
 
 DB.match [] ``a-b < c``;
 INT_SUB_0;
 INT_LT_SUB_RADD;
 OmegaMath.sum_normalise ``5 + 2 + 2*x - (f y :int) ``;
 val term = ``(z:int) = (5:int) + (2:int) + 2 * (x:int) - (y:int) ``;
 normalise_eq ``(z:int) = (5:int) + (2:int) + 2 * (x:int) - (y:int) ``;
 
  val goal : goal = 
 ([``T ⇎ F``, 
 ``((x:int) = 1) ∨ ((x:int) − 2 = 0) ∨ ¬P T ∨ (x:int) − 1 ≠ 0``, 
 ``((x:int) = 1) ∨ P F ∨ (x:int) − 1 ≠ 0``, 
 ``((x:int) = 1) ∨ (x:int) ≠ 2 ∨ (x:int) − 1 ≠ 0``, 
 ``(x:int) ≠ 1 ∨ (x:int) ≠ 2 ∨ (x:int) − 1 ≠ 0``, 
 ``(x:int) ≠ 1 ∨ P T ∨ (x:int) − 1 ≠ 0``, 
 ``(x:int) ≠ 1 ∨ ((x:int) − 2 = 0) ∨ ¬P T ∨ (x:int) − 1 ≠ 0``, 
 ``(x:int) ≠ 1 ∨ ((x:int) − 2 = 0) ∨ ¬P F ∨ ((x:int) − 1 = 0)``, 
 ``(x:int) ≠ 1 ∨ P T ∨ ((x:int) − 1 = 0)``, 
 ``(x:int) ≠ 1 ∨ (x:int) ≠ 2 ∨ ((x:int) − 1 = 0)``, 
 ``((x:int) = 1) ∨ (x:int) ≠ 2 ∨ ((x:int) − 1 = 0)``, 
 ``((x:int) = 1) ∨ P F ∨ ((x:int) − 1 = 0)``, 
 ``((x:int) = 1) ∨ ((x:int) − 2 = 0) ∨ ¬P F ∨ ((x:int) − 1 = 0)``
 ], 
 ``P T ∨ -(x:int) + 1 ≠ 0``);
 ;
SIMP_CONV (simpLib.mk_simpset[intSimps.INT_ARITH_ss]) [] ``(x:int) + y = 4 + 5``;
 REDUCE_CONV ``(x:int) − 2 = 1``;
 Cooper.COOPER_CONV ``(x:int) − 2 = 1``;
 intSimps.ADDL_CANON_CONV ``(x:int) − 2 = 0``;
 
val goal : goal = ([``!f. f (0:int) = y:int``,``g (0:int) = (0:int)``,
                  ``(y:int)+3=0``],F); 

val cooperthml = mk_cooperthml goal;
val hypl = fst goal;

val hypl2 = keep_strongest_hyp hypl;

val goal : goal =
 ([``0 ≠ (x:int) + -(y:int)``,
 ``((n2s (x:int):int) = (n2s (y:int):int)) ∨ (0 = (x:int) + -(y:int))``,
 ``((n2s (y:int):int) ≠ (n2s (x:int):int)) ∨ ((x:int) + -(y:int) ≠ 0)``], 
 ``F``);
 
val goal : goal =
 ([``(x:int) = (e1:int)``, ``(y:int) = f (e1:int)``,
  ``(e1:int) = g (x:int)``, ``(x:int) ≠ (y:int)``, ``(e1:int) = g (y:int)``,
  ``(x:int) = f (g (x:int):int)``],    
   ``F``)  
   

val goal : goal = ([],``((f a b = 3:int) /\ (f a = g)) ==> (g b = 2 + 1:int)``);
val goal : goal = ([``!f. f (0:int) (x:num) = 2:int``,``(y:int)+3 = 0``],F);

(* problem 1 *)

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


BEAGLE_PROVE thml goal;


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
val goal : goal = ([]
val th1 = mk_thm ([],
`` ∀s.
     FINITE s ⇒
     ∀lo X x.
       x ∈ X ∧ (s = {y | (y,x) ∈ lo}) ∧ linear_order lo X ∧
       finite_prefixes lo X ⇒
       ∃i. LNTH i (LUNFOLD linear_order_to_list_f lo) = SOME x ``);
val th2 = mk_thm ([], 
``∀r s. finite_prefixes r s ⇔ ∀e. e ∈ s ⇒ FINITE {e' | (e',e) ∈ r}``);
val goal : goal = ([],``P ((x:int) = x + 1) ==> P F ``); 
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



 
 