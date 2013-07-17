signature monomorph =
sig

  include Abbrev

  val all_subst : term -> ((hol_type,hol_type)subst) list
  val monomorph : term -> term
  
end