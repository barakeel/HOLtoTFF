signature blibPrinttff =
sig
  
  include Abbrev
  
  val write_tff : string -> goal -> 
                  ((hol_type * int) * string) list *
                  (term * string) list *
                  (term * string) list *
                  (term * string) list 
end