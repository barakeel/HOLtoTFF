signature monomorph =
sig

type thm = Thm.thm
type term = Term.term
type fvcinfos =
  { term : Term.term, 
    def : thm option, 
    axiom : bool,
    replace : bool }

type hol_type = Type.hol_type
type subst = {redex: hol_type, residue: hol_type} list










end