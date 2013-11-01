signature blibDatatype =
sig

include Abbrev
  
datatype STRUCTVAR = Freevar | Boundvar | Constvar

datatype STRUCTTERM = Numeral | Integer | Var | Const | Comb | Abs  
fun structterm : term -> STRUCTTERM

datatype STRUCTTYPE = Booltype | Numtype | Alphatype | Leaftype | 
                      Funtype | Prodtype | Nodetype
fun structtype : hol_type -> STRUCTTYPE 

datatype STRUCTCOMB = 
  Conj | Disj | Neg | Imp_only | Forall | Exists | 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated   
  Othercomb
fun structcomb : term -> STRUCTCOMB
fun is_connector : term -> bool
fun is_numarith  : term -> bool
fun is_intarith  : term -> bool

datatype STRUCTARITY = Binop | Unop | Quant | Otherarity
fun structarity : term -> STRUCTARITY

datatype STRUCTLEAFC = True | False | Otherleafc
fun structleafc : term -> STRUCTLEAFC

end