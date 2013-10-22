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
  val termarith : term -> TERMARITH
  val is_intarith : term -> bool
  
  datatype LEAFCONST = True | False | Newleafconst
  val leafconst : term -> LEAFCONST
  
  datatype TERMSTRUCTURE = Numeral | Integer | Var | Const | Comb | Abs  
  val termstructure : term -> TERMSTRUCTURE  
    
  datatype CONNECTOR = Conj | Disj | Neg | Imp_only | Forall | Exists | Notconnector
  val connector : term -> CONNECTOR
  val is_connector : term -> bool 
 
  datatype VARCAT = Numeralvar | Integervar | Freevar | Boundvar | Constvar 
  val typecat : hol_type -> TYPECAT


end
