signature blibPrinttff =
sig
  
  include Abbrev
  
  val pptff_term : ppstream -> term -> 
                   ((hol_type * int) * string) list *
                   (term * string) list *
                   (term * string) list *
                   (term * string) list -> 
                   unit
  val pptff_tff : ppstream -> (int * string) -> goal -> 
                  ((hol_type * int) * string) list *
                  (term * string) list *
                  (term * string) list *
                  (term * string) list
  val write_tff : string -> (int * string) -> goal -> bool -> 
                  ((hol_type * int) * string) list *
                  (term * string) list *
                  (term * string) list *
                  (term * string) list 

end