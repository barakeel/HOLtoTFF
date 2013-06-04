signature name =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type
  type VARCAT = extractvar.VARCAT

  val namealphal : term list -> (hol_type * string) list 
  val namesimpletype : hol_type -> (hol_type * string) list -> string
  val nametype : hol_type -> int -> (hol_type * string) list -> string

  (* fcv : free variable or constant *)
  val namefvcl : (term * int * VARCAT) list -> (term * int * string) list 
  val addtypenm : (term * int * string) list -> (hol_type * string) list -> (term * int * string * string) list 

  val namenumeral : term -> string
  val namebvn : term -> int -> string
  val nameaxioml : term list -> (term * string) list
  
end
