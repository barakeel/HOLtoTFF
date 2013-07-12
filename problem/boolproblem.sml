structure boolproblem :> boolproblem =
struct

open HolKernel

(* implication *)
val pb_bool1 = 
  let 
    val hyp1 = ``P:bool``
    val hyp2 = ``P ==> Q``
    val conclt = ``Q:bool``
  in
    mk_thm ([hyp1,hyp2],conclt)
  end
(* *)
val pb_bool2 =
  let val conclt = ``((P ==> Q) ==> P) ==> Q `` in 
    mk_thm ([],conclt)
  end
(* pierce law *)
val pb_bool3 =
   let val conclt = ``((P ==> Q) ==> P) ==> P `` in
     mk_thm ([],conclt)
   end
(* distributivity *)
val pb_bool4 =
  let 
    val hyp1 = `` A /\ (B \/ C) ``
    val conclt = ``(A /\ B) \/ (A /\ C) ``
  in
    mk_thm ([hyp1],conclt)
  end
(* random sat *)
val pb_bool5 =
  let val conclt = ``(A /\ B /\ C) \/ (A /\ D /\ ~C) \/ (B /\ ~D /\ ~C)`` in
    mk_thm ([],conclt)
  end

end
