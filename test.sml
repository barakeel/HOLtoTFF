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
load "blibBrule"; open blibBrule;
load "beagle"; open beagle;
*)


(* todo:
- optimisation (especially) on how to instantiate and paramodulate to
*)
BEAGLE_PROVE [] goal;
BEAGLE_ORACLE
BEAGLE_NF_TAC [] goal
metisTools.FO_METIS_TAC [] goal;
val goal : goal = ([``2=3``],``3=2``);
get_atomlthml [] goal;
mk_bcooperthml [] goal;

val goal:goal = ([``∀n. (s2n :int -> int) (n2s (n:int)) = (n:int)``], 
``((n2s :int -> int) (x:int) = n2s (y:int)) ⇔ ((x:int) = (y:int))``);

val goal:goal = ([``x+1=y``,``y+1=z``],``x+2=z``);

val term1 = ``2 = App g 0``;
val term2 = ``0 = App g 0``;
val goal : goal = ([],mk_disj(mk_neg term1,mk_neg term2));
val thm = (snd (Cooper.COOPER_TAC goal)) [];

val goal = ([``2*x < 4``],``x<2``);
val thml = [];
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``],F);


BEAGLE_ORACLE [] goal;
val finalgoal = (hd o fst) (BEAGLE_NF_TAC [] goal);
val goal1 = (hd o fst) (list_ASSUME_TAC cooperthml finalgoal);

val goal2 = (hd o fst) (metisTools.FO_METIS_TAC [] goal1);


fun has_int_type term = (type_of term = ``:int``); 
find_terms has_int_type ``-5``;

val goal : goal = ([],``(h (x:'a) y z :bool) /\ (h (x:'a) = g)``);
;

show_assums := true;

(* success *)

val goal:goal = ([``∀n. (s2n :num -> num) (n2s (n:num)) = (n:num)``], 
``((n2s :num -> num) (x:num) = n2s (y:num)) ⇔ ((x:num) = (y:num))``);
BEAGLE_NF_TAC [] goal;
val cooperthml = mk_bcooperthml [] goal;
val atomlthml = get_atomlthml [] goal;


val thml = [];


val thml = [];
val goal : goal = ([``!f. f (0:num) = 2:num``,``g (0:num) = (0:num)``],F);


val thml = [];
val goal : goal = (
[
``(g (0:int) = (0:int)) ==> ~(g (0:int) = (2:int))``, 
``!f. f (0:int) = (2:int)``,
``g (0:int) = (0:int)``
],
 F);
OmegaMath.sum_normalise ``(x:int) + (y:int)``;
OmegaMath.sum_normalise ``(y:int) + (x:int)``;

val goal : goal = ([``P (x=2):bool``],``P (x-2=0):bool``);

val (finalgoal,_) = BEAGLE_NF_TAC [] goal;


BEAGLE_TAC [] goal;
mk_bcooperthml [] goal;
metisTOOLS


val goal : goal = ([``P (x=2):bool ``,``(x:int)=y``],``P (y-2=0):bool``);
BEAGLE_NF_TAC [] goal;


val thml = [];
val goal : goal = 
([],``((f a b = 3:int) /\ (f a = g)) ==> (g b = (2+1:int))``);


val th1 = mk_thm ([],``!z. (z = 2) = (z - 2 = 0)``);
val th2 = mk_thm ([],``~(x = 2) = ~(x - 2 = 0)``);
val thml = [th1];

METIS_COOPER_CNF goal;
 val cooperthml = mk_bcooperthml goal;

(snd (Cooper.COOPER_TAC goal)) [];

val (newgoal,_) = BEAGLE_NF_TAC [] goal;
(snd (metisTools.FO_METIS_TAC thml (hd newgoal))) [];
(* need a normalisation *)
metisTools.METIS_PROVE thml goal;

 
 (snd (metisTools.FO_METIS_TAC thml goal)) [];

metisTools.FO_METIS_TAC thml goal;
(* test 
val term = ``∀x. (x = 5) \/ (x < 5)``

val term = ``(f x = 5) \/ (f x < 5)``;
fun has_type ty term = type_of term = ty

val int_type = ``:int``;
find_terms (has_type int_type) (``-5``);
val goal = ([term],F);
val goal = (terml,F);
*)

val term1 = lhs (concl (normalForms.CNF_CONV ``A ==> ~B``));

aconv ``A \/ B`` ``B \/ A``;
normalForms.CNF_CONV ``B ==> ~A``;
Term.compare (``A:bool``,``B:bool``);
less_term;

val terml = [``∀x. (x = 5)``,``~(2 = 5) \/ ~(3 = 5)``];

val thml = [];
val goal : goal = 
([``n2s (s2n (s:num):num) = s``],
``∀s. ∃n. (s:num) = n2s (n:num)``);

val thml = [];
val goal : goal = 
([``!s. n2s (s2n (s:int):int) = s``],
``∀s. ∃n. (s:int) = n2s (n:int)``);

val thml = [];
val goal : goal = 
([``n2s (s2n (s:'a):'a) = s``],
``∀s. ∃n. (s:'a) = n2s (n:'a)``);
 
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

BEAGLE_NF_TAC thml goal;


(* PROBLEM TEST *)   
val thml = [];
val goal : goal = ([``(x:num = 5) /\ (y:num = 2)``],``x:num = 5``);
BEAGLE_TAC thml goal
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



 
 