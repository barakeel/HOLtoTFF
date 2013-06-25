signature axiomordef =
sig

  type term     = Term.term
  type hol_type = Type.hol_type
  type fvcinfos =
    { term : Term.term, 
      def : thm option, 
      axiom : bool,
      replace : bool }
(* need to recursively reduce inside the term lambda abstraction *)
  val default_constchart : unit -> fvcinfos list

end