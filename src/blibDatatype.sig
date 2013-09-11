signature blibDatatype =
sig

  include Abbrev

  datatype TYPECAT = Booltype | Numtype | Alphatype | Leaftype |
                     Funtype | Prodtype | Nodetype
  datatype NODECONST = Eq | Add | Minus | Mult | Less | Greater | Geq | Leq |
                       Newnodeconst
  datatype LEAFCONST = True | False | Newleafconst
  datatype TERMSTRUCTURE = Numeral | Var | Const | Comb | Abs  
  datatype CONNECTOR = Conj | Disj | Neg | Imp_only | Forall | Exists | App
  
  datatype VARCAT = Numeralvar | Freevar | Boundvar | Constvar 
  
  val typecat : hol_type -> TYPECAT
  val termstructure : term -> TERMSTRUCTURE  
  val nodeconst : term -> NODECONST
  val leafconst : term -> LEAFCONST
  val connector : term -> CONNECTOR

end
