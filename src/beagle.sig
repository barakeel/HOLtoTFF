signature beagle =
sig
  
  include Abbrev
  
  val beagle_tac_aux : string -> thm list -> tactic
  val beagle_tac_poly : string -> thm list -> tactic
  val BEAGLE_TAC : thm list -> tactic
 
  (* beagle_nf *)
  val beagle_nf : string -> thm list -> goal -> goal
  val beagle_nf_val : thm list -> goal -> rule
  
  val problem_to_goal : thm list -> goal -> goal 
  val problem_to_goal_val : thm list -> goal -> rule
  
  val beagle_convert : goal -> goal 
  val beagle_convert_val : goal -> rule
  val beagle_conv : conv
 
  val beagle_clauseset : goal -> goal 
  val beagle_clauseset_val : goal -> rule 
  val erase_exists : goal -> goal
  val erase_exists_val : goal -> rule
  val forall_conjuncts : goal -> goal
  val forall_conjuncts_val : goal -> rule
  val strip_conj_hyp : goal -> goal
  val strip_conj_hyp_val : goal -> rule
  val erase_forall : goal -> goal
  val erase_forall_val : goal -> rule
  val add_axioms : goal -> goal
  val add_axioms_val : goal -> rule
  val add_higher_order : goal -> goal
  val add_higher_order_val : goal -> rule

  (* beagle_interact *)
  val beagle_interact : string -> goal -> unit

end