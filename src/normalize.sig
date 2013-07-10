signature normalize =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type thm = Thm.thm
(* input is a list of thm *)
  (* conv *)
  val beta_conv : term -> thm 
  val eta_conv : term -> thm
  val bool_conv : term -> thm 
  val fun_conv : term -> thm
  val app_conv : term -> thm
  val num_conv : term -> thm
  val predicate_conv : term -> thm
  (* rewrite *)
  (* val skolem_rewrite : terml -> term varl hypterm thm *)

 
end
