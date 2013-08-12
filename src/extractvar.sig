signature extractvar =
sig

  include Abbrev
  type VARCAT = mydatatype.VARCAT

  val erase_number : ((term * int) * VARCAT) list -> 
                     ((term * int) * VARCAT) list
  
  val extract_var : term -> ((term * int) * VARCAT) list 
  val extract_varl : term list -> ((term * int) * VARCAT) list 
                    
  val get_bval : term -> (term * int) list 
  val get_fval : term -> (term * int) list 
  val get_cal : term -> (term * int) list 
  val get_fvcal : term -> (term * int) list 
  
  val get_bvl : term -> term list 
  val get_fvl : term -> term list 
  val get_cl : term -> term list 
  val get_fvcl : term -> term list 
  val all_var : term -> term list 
   
  val all_varl : term list -> term list
    
  val get_bvl_thm  : thm -> term list
  val get_fvl_thm  : thm -> term list
  val get_cl_thm   : thm -> term list
  val get_fvcl_thm : thm -> term list
  val all_var_thm  : thm -> term list

  val get_fvl_goal  : goal -> term list
  val get_bvl_goal  : goal -> term list
  val get_cl_goal   : goal -> term list
  val get_fvcl_goal : goal -> term list 
  val all_var_goal  : goal -> term list
  
end