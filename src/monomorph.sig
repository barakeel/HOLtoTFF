signature monomorph =
sig

  include Abbrev
  
  (* test *)
  val is_polymorph : term -> bool
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : (thm list * goal) -> bool 
  
  (* arithmetic *)
  val add_subst : ((hol_type,hol_type)subst) -> ((hol_type,hol_type)subst) ->
                  ((hol_type,hol_type)subst) list
  val multone_subst : ((hol_type,hol_type)subst) -> 
                    ((hol_type,hol_type)subst) list ->
                    ((hol_type,hol_type)subst) list
  val mult_subst : ((hol_type,hol_type)subst) list -> 
                   ((hol_type,hol_type)subst) list ->
                   ((hol_type,hol_type)subst) list
  val list_mult_subst : ((hol_type,hol_type)subst) list list ->
                        ((hol_type,hol_type)subst) list
  (* could be in list tools *)
  val get_maxsubstl : ((hol_type,hol_type)subst) list -> 
                      ((hol_type,hol_type)subst) list
  (* subst *)
  val is_matchable: term -> term -> bool
  val match_c_cl: term -> term list -> ((hol_type,hol_type)subst) list
  
  val inst_cll : ((hol_type,hol_type)subst) list list ->
                 term list list ->
                 term list list
  
  val create_substl : term list -> term list  ->
                      ((hol_type,hol_type)subst) list
  val create_substll : term list list -> term list ->
                       ((hol_type,hol_type)subst) list list
  val repeat_create_substll : (term list list * term list) ->
                              ((hol_type,hol_type)subst) list list ->
                              ((hol_type,hol_type)subst) list list
               
  (* monomorphisation *)
  val monomorph_pb : (thm list * goal) -> (thm list * goal)
 
end