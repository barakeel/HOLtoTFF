signature monomorph =
sig

  include Abbrev
  
  (* test *)
  val is_polymorph : term -> bool
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : (thm list * goal) -> bool 
  
  (* subst *)
  val match_cl_to_cl : term list -> term list ->
                           ((hol_type,hol_type)subst) list
  val inst_cll : ((hol_type,hol_type)subst) list list ->
                 term list list ->
                 term list list
  
  val create_substl : term list -> (term list list * term list) ->
                            ((hol_type,hol_type)subst) list
  val create_substll : (term list list * term list) ->
                       ((hol_type,hol_type)subst) list list
  val repeat_create_substll : (term list list * term list) ->
                              ((hol_type,hol_type)subst) list list ->
                              int list ->
                              ((hol_type,hol_type)subst) list list
               
  (* monomorphisation *)
  val monomorph_pb : (thm list * goal) -> (thm list * goal)
 
end