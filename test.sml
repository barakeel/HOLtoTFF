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
load "blibNumInt"; open blibNumInt;
load "blibReader"; open blibReader;
load "blibReplayer"; open blibReplayer;
load "blibConv"; open blibConv;
load "blibMonomorph"; open blibMonomorph;
load "blibBrule"; open blibBrule;
load "beagle"; open beagle;
*)
show_assums:=true;


beagle_proof [] goal;
BEAGLE_ORACLE [] goal;
BEAGLE_NF_TAC [] goal;
metisTools.FO_METIS_TAC [] goal;


val goal:goal = ([``x+1=y``,``y+1=z``],``x+2=z``);
val goal : goal = ([``P (x=2):bool ``,``(x:int)=y``],``P (y-2=0):bool``);
val goal = ([``2*x < 4``],``x<2``);
val goal : goal = ([``!f. f (0:int) = 2:int``,``g (0:int) = (0:int)``],F);
val goal : goal = ([``!f. f (0:num) = 2:num``,``g (0:num) = (0:num)``],F);
val goal:goal = ([``∀n. (s2n :int -> int) (n2s (n:int)) = (n:int)``], 
``((n2s :int -> int) (x:int) = n2s (y:int)) ⇔ ((x:int) = (y:int))``);
val goal:goal = ([``∀n. (s2n :num -> num) (n2s (n:num)) = (n:num)``], 
``((n2s :num -> num) (x:num) = n2s (y:num)) ⇔ ((x:num) = (y:num))``);
val goal : goal = 
([],``((f a b = 3:int) /\ (f a = g)) ==> (g b = (2+1:int))``); 
(* nlia test *)
val goal = ([``(x * y = 4)``],``(y * x = 4)``);     
(* monomorphisation *)
val th1 = mk_thm ([],``!x:'c y. x ∈ {y} = (x = y)``);
val th2 = mk_thm ([],``!(P:'a-> bool) x. x ∈ P = P x``);
val thml = [th1,th2];
val goal:goal = ([], ``!x:num. (x = z) = {z} x``);
BEAGLE_ORACLE thml goal;
(* funconv *)  
val goal : goal = ([],``(!y:num -> num -> num . P y) ==> (P (\x y. x + y))`` );



 
 