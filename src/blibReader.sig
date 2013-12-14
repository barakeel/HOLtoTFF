signature blibReader =
sig
  
  include Abbrev

  val read_proof : string -> 
                   (((hol_type * int) * string) list *
                    (term * string) list *
                    (term * string) list *
                    (term * string) list )
                   -> ((int list * term) list)

end