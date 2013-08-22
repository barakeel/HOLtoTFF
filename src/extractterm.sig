signature extractterm =
sig

  include Abbrev
  
   val all_subterm : term -> term list
  
end