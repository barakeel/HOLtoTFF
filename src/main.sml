structure main :> main =
struct

open HolKernel 
(* input is an axioml and a conjecture *)
(* goal is not special anymore *)
(* output: thm *)

fun unify axioml =
  let val newaxioml = map DISCH_ALL axioml in
    LIST_CONJ newaxioml
  end

  (* should maybe monomorph to itself *)
fun initial_assume axioml conjecture =
  let 
    val prop1 = concl (unify axioml) 
    val prop2 = concl (DISCH_ALL conjecture) 
  in
    ASSUME (mk_conj (prop1, mk_neg prop2))
  end


(* if you have an hypothesis in a conv it's not a problem *)
(*
A B C |- F
et
D |- B <=> (D => B')
 B' |- D => B'
A D => B' C D |-F
A B' C D |- F
*)

(* should make dictionnaries *)

(* free_var x_str *)
(* bound X_str *)
(* constant c_str *)
(* created bool b0 or B0*)
(* created fonction f0 or F0 *)
(* created app0 ... *)
(* skolem constant printed sk0_str *)
(* should create different names for every different constant created 
, reduce after if there's two of the same constant appearing with the same name *)
(* same definition  at the same level *) 



end