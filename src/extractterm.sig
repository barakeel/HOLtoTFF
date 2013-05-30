signature extractterm =
sig

  type term     = Term.term
(* fvc : free variable or constant*)
  val getfvcl : term list -> term list 

end
