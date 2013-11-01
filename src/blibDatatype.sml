structure blibDatatype :> blibDatatype =
struct

open HolKernel Abbrev boolLib numSyntax (*intSyntax*)
     blibBtools

fun DATATYPE_ERR function message =
  HOL_ERR{origin_structure = "blibDatatype",
	        origin_function = function,
          message = message}

datatype STRUCTVAR = Freevar | Boundvar | Constvar

datatype STRUCTTERM = Numeral | Integer | Var | Const | Comb | Abs  

fun structterm term =
  switchargerr term
    [
    (numSyntax.is_numeral ,Numeral),
    (intSyntax.is_int_literal , Integer),
    (is_var     ,Var),
    (is_const   ,Const),
    (is_comb    ,Comb),
    (is_abs     ,Abs)
    ]
    (DATATYPE_ERR "structterm" "unknown structterm")   


datatype STRUCTTYPE = Booltype | Numtype | Alphatype | Leaftype | 
                      Funtype | Prodtype | Nodetype

fun structtype holtype =
  case (holtype = ``:bool``,holtype = ``:num``,is_vartype holtype) of
    (true,_,_) => Booltype
  | (_,true,_) => Numtype
  | (_,_,true) => Alphatype
  | (_,_,_) => case (dest_type holtype) of  
                 (_,[]) => Leaftype
               | ("fun",_) => Funtype
               | ("prod",_) => Prodtype
               | _ => Nodetype

datatype STRUCTCOMB = 
  Conj | Disj | Neg | Imp_only | Forall | Exists | 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated   
  Othercomb

fun structcomb term =
  switcharg term
    [  
    (is_conj     ,Conj),
    (is_disj     ,Disj),
    (is_neg      ,Neg),
    (is_imp_only ,Imp_only),
    (is_forall   ,Forall),
    (is_exists   ,Exists)
    (is_eq       ,Eq), 
    (numSyntax.is_plus     ,Plusn),
    (numSyntax.is_minus    ,Minusn),
    (numSyntax.is_mult     ,Multn),
    (numSyntax.is_less     ,Lessn),
    (numSyntax.is_greater  ,Greatern),
    (numSyntax.is_geq      ,Geqn),
    (numSyntax.is_leq      ,Leqn),
    (intSyntax.is_plus     ,Plusi),
    (intSyntax.is_minus    ,Minusi),
    (intSyntax.is_mult     ,Multi),
    (intSyntax.is_less     ,Lessi),
    (intSyntax.is_great    ,Greateri),
    (intSyntax.is_geq      ,Geqi),
    (intSyntax.is_leq      ,Leqi),
    (intSyntax.is_negated  ,Negated)
    ]
    Othercomb

fun is_connector term =
  is_conj term orelse
  is_disj term orelse
  is_neg term orelse
  is_imp_only term orelse
  is_forall term orelse
  is_exists term

fun is_numarith term =
  numSyntax.is_plus term orelse
  numSyntax.is_minus term orelse
  numSyntax.is_mult term orelse
  numSyntax.is_less term orelse
  numSyntax.is_great term orelse  
  numSyntax.is_geq term orelse
  numSyntax.is_leq term

fun is_intarith term =
  intSyntax.is_plus term orelse
  intSyntax.is_minus term orelse
  intSyntax.is_mult term orelse
  intSyntax.is_less term orelse
  intSyntax.is_great term orelse  
  intSyntax.is_geq term orelse
  intSyntax.is_leq term orelse
  intSyntax.is_negated term


datatype STRUCTARITY = Binop | Unop | Quant | Otherarity

fun structarity term =
  switcharg term 
    [
    (is_conj     ,Binop),
    (is_disj     ,Binop),
    (is_neg      ,Unop),
    (is_imp_only ,Binop),
    (is_forall   ,Quant),
    (is_exists   ,Quant),
    (is_eq       ,Binop), 
    (numSyntax.is_plus     ,Binop),
    (numSyntax.is_minus    ,Binop),
    (numSyntax.is_mult     ,Binop),
    (numSyntax.is_less     ,Binop),
    (numSyntax.is_greater  ,Binop),
    (numSyntax.is_geq      ,Binop),
    (numSyntax.is_leq      ,Binop),
    (intSyntax.is_plus     ,Binop),
    (intSyntax.is_minus    ,Binop),
    (intSyntax.is_mult     ,Binop),
    (intSyntax.is_less     ,Binop),
    (intSyntax.is_great    ,Binop),
    (intSyntax.is_geq      ,Binop),
    (intSyntax.is_leq      ,Binop),
    (intSyntax.is_negated  ,Unop)
    ]
    Otherarity



datatype STRUCTLEAFC = True | False | Otherleafc

fun structleafc term =
  switcharg term
    [
    (equal T ,True),
    (equal F ,False)
    ]
    Otherleafc





end

