signature name =
sig
  
  type term     = Term.term
  type hol_type = Type.hol_type

  val namealphal : term list -> (hol_type * string) list 
  val nametype : hol_type -> (hol_type * string) list -> string

  (* fcv : free variable or constant *)
  val getfvcl : term list -> term list
  val namefvcl : term list -> (term * string) list 
  (* bv : bound variable *)
  val namebvn : term -> int -> string 

  val nameaxioml : term list -> (term * string) list
  
end
