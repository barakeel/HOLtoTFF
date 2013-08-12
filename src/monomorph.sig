signature monomorph =
sig

  include Abbrev

  val all_subst : hol_type list -> hol_type list -> 
                  ((hol_type,hol_type)subst) list
  val all_subst_thm : thm -> goal -> ((hol_type,hol_type)subst) list               
  val monomorph : ((hol_type,hol_type)subst) list -> thm -> thm 
  val monomorph_pb_c : thm list -> goal -> thm list

end