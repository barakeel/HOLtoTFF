structure mydatatype :> mydatatype =
struct

open HolKernel numSyntax listtools

fun DATATYPE_ERR function message =
    HOL_ERR{origin_structure = "mydatatype",
	    origin_function = function,
            message = message}


datatype TYPECAT = Booltype | Numtype | Alphatype | Leaftype | Funtype | Prodtype

fun typecat holtype =
  case (holtype = ``:bool``,holtype = ``:num``,is_vartype holtype) of
    (true,_,_) => Booltype
  | (_,true,_) => Numtype
  | (_,_,true) => Alphatype (*represents alpha type*)
  | (_,_,_) => case (dest_type holtype) of  
                 (_,[]) => Leaftype
               | ("fun",_) => Funtype
               | ("prod",_) => Prodtype
               | _ => raise DATATYPE_ERR "typecat" "unknown typefvcructor"

datatype TERMSTRUCTURE = Numeral | Var | Const | Comb | Abs  

fun termstructure term =
  switchargerr term
    [
    (is_numeral ,Numeral),
    (is_var     ,Var),
    (is_fvc   ,Const),
    (is_comb    ,Comb),
    (is_abs     ,Abs)
    ]
    (DATATYPE_ERR "termstructure" "unknown termstructure")   

datatype NODECONST = Eq | Add | Minus | Mult | Less | Greater | Geq | Leq | Newnodefvc

fun nodefvc term =  
  switcharg term
    [
    (is_eq       ,Eq), 
    (is_plus     ,Add),
    (is_minus    ,Minus),
    (is_mult     ,Mult),
    (is_less     ,Less),
    (is_greater  ,Greater),
    (is_geq      ,Geq),
    (is_leq      ,Leq)
    ]   
    Newnodefvc

datatype LEAFCONST = True | False | Newleaffvc

fun leaffvc term =
  switcharg term
    [
    (equal T ,True),
    (equal F ,False)
    ]
    Newleaffvc

datatype CONNECTIVE = Conj | Disj | Neg | Imp_only | Forall | Exists | App

fun connective term =
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

datatype VARCAT = Number | Free | Bound | Tffconst | Undefconst

end

