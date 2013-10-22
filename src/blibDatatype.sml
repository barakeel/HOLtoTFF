structure blibDatatype :> blibDatatype =
struct

open HolKernel Abbrev boolLib numSyntax (*intSyntax*)
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

datatype TERMSTRUCTURE = Numeral | Integer | Var | Const | Comb | Abs  

fun is_false term = false

fun termstructure term =
  switchargerr term
    [
    (numSyntax.is_numeral ,Numeral),
    (is_false (*intSyntax.is_int_literal*) , Integer),
    (is_var     ,Var),
    (is_const   ,Const),
    (is_comb    ,Comb),
    (is_abs     ,Abs)
    ]
    (DATATYPE_ERR "termstructure" "unknown termstructure")   



datatype TERMARITH = 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated |
  Newtermarith

fun termarith term =  
  switcharg term
    [
    (is_eq       ,Eq), 
    (numSyntax.is_plus     ,Plusn),
    (numSyntax.is_minus    ,Minusn),
    (numSyntax.is_mult     ,Multn),
    (numSyntax.is_less     ,Lessn),
    (numSyntax.is_greater  ,Greatern),
    (numSyntax.is_geq      ,Geqn),
    (numSyntax.is_leq      ,Leqn),
    (* to be removed for numeral test *)
    (intSyntax.is_plus     ,Plusi),
    (intSyntax.is_minus    ,Minusi),
    (intSyntax.is_mult     ,Multi),
    (intSyntax.is_less     ,Lessi),
    (intSyntax.is_great    ,Greateri),
    (intSyntax.is_geq      ,Geqi),
    (intSyntax.is_leq      ,Leqi),
    (intSyntax.is_negated  ,Negated)
    ]   
    Newtermarith

fun is_intarith term =
  intSyntax.is_plus term orelse
  intSyntax.is_minus term orelse
  intSyntax.is_mult term orelse
  intSyntax.is_less term orelse
  intSyntax.is_great term orelse  
  intSyntax.is_geq term orelse
  intSyntax.is_leq term orelse
  intSyntax.is_negated term

datatype LEAFCONST = True | False | Newleafconst

fun leafconst term =
  switcharg term
    [
    (equal T ,True),
    (equal F ,False)
    ]
    Newleafconst

datatype CONNECTOR = Conj | Disj | Neg | Imp_only | Forall | Exists | Notconnector

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
    Notconnector

fun is_connector term =
  is_conj term orelse
  is_disj term orelse
  is_neg term orelse
  is_imp_only term orelse
  is_forall term orelse
  is_exists term

datatype VARCAT = Numeralvar | Integervar | Freevar | Boundvar | Constvar

end

