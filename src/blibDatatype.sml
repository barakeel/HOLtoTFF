structure blibDatatype :> blibDatatype =
struct

open HolKernel Abbrev boolLib numSyntax
     blibBtools

fun DATATYPE_ERR function message =
  HOL_ERR{origin_structure = "blibDatatype",
	        origin_function = function,
          message = message}


datatype TYPECAT = Booltype | Numtype | Alphatype | Leaftype | 
                   Funtype | Prodtype | Nodetype

fun typecat holtype =
  case (holtype = ``:bool``,holtype = ``:num``,is_vartype holtype) of
    (true,_,_) => Booltype
  | (_,true,_) => Numtype
  | (_,_,true) => Alphatype
  | (_,_,_) => case (dest_type holtype) of  
                 (_,[]) => Leaftype
               | ("fun",_) => Funtype
               | ("prod",_) => Prodtype
               | _ => Nodetype

datatype TERMSTRUCTURE = Numeral | Var | Const | Comb | Abs  

fun termstructure term =
  switchargerr term
    [
    (is_numeral ,Numeral),
    (is_var     ,Var),
    (is_const   ,Const),
    (is_comb    ,Comb),
    (is_abs     ,Abs)
    ]
    (DATATYPE_ERR "termstructure" "unknown termstructure")   

datatype NODECONST = Eq | Plus | Minus | Mult | Less | Greater | Geq | Leq | Newnodeconst

fun nodeconst term =  
  switcharg term
    [
    (is_eq       ,Eq), 
    (is_plus     ,Plus),
    (is_minus    ,Minus),
    (is_mult     ,Mult),
    (is_less     ,Less),
    (is_greater  ,Greater),
    (is_geq      ,Geq),
    (is_leq      ,Leq)
    ]   
    Newnodeconst

datatype LEAFCONST = True | False | Newleafconst

fun leafconst term =
  switcharg term
    [
    (equal T ,True),
    (equal F ,False)
    ]
    Newleafconst

datatype CONNECTOR = Conj | Disj | Neg | Imp_only | Forall | Exists | App

fun connector term =
  switcharg term
    [  
    (is_conj     ,Conj),
    (is_disj     ,Disj),
    (is_neg      ,Neg),
    (is_imp_only ,Imp_only),
    (is_forall   ,Forall),
    (is_exists   ,Exists)
    ]
    App

datatype VARCAT = Numeralvar | Freevar | Boundvar | Constvar

end

