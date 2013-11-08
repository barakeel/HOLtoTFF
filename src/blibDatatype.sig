signature blibDatatype =
sig

include Abbrev

(* writer *)  
datatype STRUCTVAR = Freevar | Boundvar | Constvar

datatype STRUCTTERM = Numeral | Integer | Var | Const | Comb | Abs  
val structterm : term -> STRUCTTERM

datatype STRUCTTYPE = Booltype | Numtype | Inttype | Alphatype | Leaftype | 
                      Funtype | Prodtype | Nodetype
val structtype : hol_type -> STRUCTTYPE 

datatype STRUCTCOMB = 
  Conj | Disj | Neg | Imp_only | Forall | Exists | 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated |  
  Othercomb
val structcomb : term -> STRUCTCOMB
val is_connector : term -> bool
val is_numarith  : term -> bool
val is_intarith  : term -> bool

datatype STRUCTARITY = Binop | Unop | Quant | Otherarity
val structarity : term -> STRUCTARITY

datatype STRUCTINFIX = Prefix | Infix | Suffix | Otherinfix
val structinfix : term -> STRUCTINFIX
val op_symb : term -> string

datatype STRUCTLEAFC = True | False | Otherleafc
val structleafc : term -> STRUCTLEAFC

(* reader *)
val is_tfffunctor : string -> bool 
val read_tfffunctor : string -> term
val is_tfftruefalse : string -> bool
val read_tfftruefalse : string -> term



end