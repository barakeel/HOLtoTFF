structure boolproblem :> boolproblem =
struct

open HolKernel

(* implication *)
val pb_bool1 = 
  let 
    val hyp1 = ``P:bool``
    val hyp2 = ``P ==> Q``
    val goal = ``Q:bool``
  in
    mk_thm ([hyp1,hyp2],goal)
  end
(* *)
val pb_bool2 =
  let val goal = ``((P ==> Q) ==> P) ==> Q `` in 
    mk_thm ([],goal)
  end
(* pierce law *)
val pb_bool3 =
   let val goal = ``((P ==> Q) ==> P) ==> P `` in
     mk_thm ([],goal)
   end
(* distributivity *)
val pb_bool4 =
  let 
    val hyp1 = `` A /\ (B \/ C) ``
    val goal = ``(A /\ B) \/ (A /\ C) ``
  in
    mk_thm ([hyp1],goal)
  end
(* random sat *)
val pb_bool5 =
  let val goal = ``(A /\ B /\ C) \/ (A /\ D /\ ~C) \/ (B /\ ~D /\ ~C)`` in
    mk_thm ([],goal)
  end

end