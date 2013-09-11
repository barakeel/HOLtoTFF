signature blibMonomorph =
sig

  include Abbrev
  
  (* test *)
  val is_polymorph : term -> bool
  val is_polymorph_thm : thm -> bool
  val is_polymorph_pb : (thm list * goal) -> bool 
  val is_monomorphable : term -> bool
  
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
  val normalize_substl : ((hol_type,hol_type)subst) list ->
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
  val inst_thm : (hol_type,hol_type)subst list -> thm -> thm
  val inst_thml : ((hol_type,hol_type)subst) list list -> thm list -> thm list
  
  val create_substl : term list -> term list  ->
                      ((hol_type,hol_type)subst) list
  val create_substll : term list list -> term list ->
                       ((hol_type,hol_type)subst) list list
  val repeat_create_substll : (term list list * term list) ->
                              ((hol_type,hol_type)subst) list list ->
                              ((hol_type,hol_type)subst) list list
               
  (* blibMonomorphisation *)
  val monomorph_pb : (thm list * goal) -> (thm list * goal)
 
end