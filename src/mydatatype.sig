signature mydatatype =
sig

  type term = Term.term
  type hol_type = Type.hol_type

  datatype TYPECAT = Booltype | Numtype | Alphatype | Simpletype | Funtype | Prodtype
  datatype TERMSTRUCTURE = Numeral | Var | Const | Comb | Abs  
  datatype NODECONST = Eq | Add | Minus | Mult | Less | Greater | Geq | Leq | Newnodeconst
  datatype LEAFCONST = True | False | Newleafconst
  datatype CONNECTIVE = Conj | Disj | Neg | Imp_only | Forall | Exists | App

  val typecat : hol_type -> TYPECAT
  val termstructure : term -> TERMSTRUCTURE  
  val nodeconst : term -> NODECONST 
  val leafconst : term -> LEAFCONST
  val connective : term -> CONNECTIVE

end
