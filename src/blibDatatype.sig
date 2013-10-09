signature blibDatatype =
sig

  include Abbrev

  datatype TYPECAT = Booltype | Numtype | Alphatype | Leaftype |
                     Funtype | Prodtype | Nodetype
  datatype TERMARITH = 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated |
  Newtermarith
  
  datatype LEAFCONST = True | False | Newleafconst
  datatype TERMSTRUCTURE = Numeral | Integer | Var | Const | Comb | Abs  
  datatype CONNECTOR = Conj | Disj | Neg | Imp_only | Forall | Exists | App
  
  datatype VARCAT = Numeralvar | Integervar | Freevar | Boundvar | Constvar 
  
  val typecat : hol_type -> TYPECAT
  val termstructure : term -> TERMSTRUCTURE  
  val termarith : term -> TERMARITH
  val leafconst : term -> LEAFCONST
  val connector : term -> CONNECTOR

end
