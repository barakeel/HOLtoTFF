signature monomorph =
sig

  include Abbrev

  val all_subst : hol_type list -> hol_type list -> 
                  ((hol_type,hol_type)subst) list
  val all_subst_thm : thm -> goal -> ((hol_type,hol_type)subst) list               
  val monomorph_rule : thm list -> goal -> thm list 

end