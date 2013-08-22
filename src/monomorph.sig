signature monomorph =
sig

  include Abbrev
  
  (* test *)
  val is_polymorph : term -> bool
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : (thm list * goal) -> bool 
  
  (* subst *)
  val create_substl_cl_cl : term list -> term list ->
                            ((hol_type,hol_type)subst) list 
  val create_substl_thm_pb : thm -> (thm list * goal) ->
                             ((hol_type,hol_type)subst) list 
  val normalize_subst : ((hol_type,hol_type)subst) ->
                        ((hol_type,hol_type)subst)
  val normalize_substl : ((hol_type,hol_type)subst) list -> 
                         ((hol_type,hol_type)subst) list 
  (* monomorphisation *)
  val inst_thm : ((hol_type,hol_type)subst) list -> thm -> thm
  val monomorph_thm_pb : thm -> (thm list * goal) -> thm
  val monomorph_pb : (thm list * goal) -> (thm list * goal)
 
end