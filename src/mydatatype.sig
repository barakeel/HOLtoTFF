signature mydatatype =
sig

  type term = Term.term
  type hol_type = Type.hol_type

  datatype TYPECAT = Booltype | Numtype | Alphatype | Leaftype | Funtype | Prodtype
  datatype NODECONST = Eq | Add | Minus | Mult | Less | Greater | Geq | Leq | Newnodefvc
  datatype LEAFCONST = True | False | Newleaffvc
  datatype TERMSTRUCTURE = Numeral | Var | Const | Comb | Abs  
  datatype CONNECTIVE = Conj | Disj | Neg | Imp_only | Forall | Exists | App
  
  datatype VARCAT = Numeralvar | Freevar | Boundvar | Constvar 

  val typecat : hol_type -> TYPECAT
  val termstructure : term -> TERMSTRUCTURE  
  val nodefvc : term -> NODECONST 
  val leaffvc : term -> LEAFCONST
  val connective : term -> CONNECTIVE

end
