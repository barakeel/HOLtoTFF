structure blibDatatype :> blibDatatype =
struct

open HolKernel Abbrev boolLib numSyntax intSyntax
     blibBtools

fun DATATYPE_ERR function message =
  HOL_ERR{origin_structure = "blibDatatype",
	        origin_function = function,
          message = message}

(* Writer *)
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


datatype STRUCTTYPE = Booltype | Numtype | Inttype | Alphatype | Leaftype | 
                      Funtype | Prodtype | Nodetype

fun structtype holtype =
  case (holtype = ``:bool``,holtype = ``:num``,
        holtype = ``:int``,is_vartype holtype) 
  of
    (true,_,_,_) => Booltype
  | (_,true,_,_) => Numtype
  | (_,_,true,_) => Inttype
  | (_,_,_,true) => Alphatype
  | _ => case (dest_type holtype) of  
           (_,[]) => Leaftype
         | ("fun",_) => Funtype
         | ("prod",_) => Prodtype
         | _ => Nodetype

datatype STRUCTCOMB = 
  Conj | Disj | Neg | Imp_only | Forall | Exists | 
  Eq | 
  Plusn | Minusn | Multn | Lessn | Greatern | Geqn | Leqn | 
  Plusi | Minusi | Multi | Lessi | Greateri | Geqi | Leqi | Negated |
  Othercomb

fun structcomb term =
  switcharg term
    [  
    (is_conj     ,Conj),
    (is_disj     ,Disj),
    (is_neg      ,Neg),
    (is_imp_only ,Imp_only),
    (is_forall   ,Forall),
    (is_exists   ,Exists),
    (is_eq       ,Eq), 
    (numSyntax.is_plus     ,Plusn),
    (numSyntax.is_minus    ,Minusn),
    (numSyntax.is_mult     ,Multn),
    (numSyntax.is_less     ,Lessn),
    (numSyntax.is_leq      ,Leqn),
    (numSyntax.is_greater  ,Greatern),
    (numSyntax.is_geq      ,Geqn),
    (intSyntax.is_plus     ,Plusi),
    (intSyntax.is_minus    ,Minusi),
    (intSyntax.is_mult     ,Multi),
    (intSyntax.is_less     ,Lessi),
    (intSyntax.is_leq      ,Leqi),
    (intSyntax.is_great    ,Greateri),
    (intSyntax.is_geq      ,Geqi),
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
  numSyntax.is_greater term orelse  
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
  case structcomb term of
    Conj     => Binop
  | Disj     => Binop
  | Neg      => Unop
  | Imp_only => Binop
  | Forall   => Quant
  | Exists   => Quant
  | Eq       => Binop
  | Plusn    => Binop
  | Minusn   => Binop    
  | Multn    => Binop
  | Lessn    => Binop
  | Leqn     => Binop
  | Greatern => Binop
  | Geqn     => Binop
  | Plusi    => Binop
  | Minusi   => Binop    
  | Multi    => Binop
  | Lessi    => Binop
  | Leqi     => Binop
  | Greateri => Binop
  | Geqi     => Binop
  | Negated  => Unop
  | Othercomb => Otherarity

datatype STRUCTINFIX = Prefix | Infix | Suffix | Otherinfix

fun structinfix term =
  case structcomb term of
    Conj     => Infix
  | Disj     => Infix
  | Neg      => Prefix
  | Imp_only => Infix
  | Forall   => Prefix
  | Exists   => Prefix
  | Eq       => Infix
  | Plusn    => Prefix
  | Minusn   => Prefix   
  | Multn    => Prefix
  | Lessn    => Prefix
  | Leqn     => Prefix
  | Greatern => Prefix
  | Geqn     => Prefix
  | Plusi    => Prefix
  | Minusi   => Prefix  
  | Multi    => Prefix
  | Lessi    => Prefix
  | Leqi     => Prefix
  | Greateri => Prefix
  | Geqi     => Prefix
  | Negated  => Prefix
  | Othercomb => Otherinfix

fun op_symb term =
  case structcomb term of
    Conj     => "&"
  | Disj     => "|"
  | Neg      => "~"
  | Imp_only => "=>"
  | Forall   => "!"
  | Exists   => "?"
  | Eq       => "="
  | Plusn    => "$sum"
  | Minusn   => "$difference"   
  | Multn    => "$product"
  | Lessn    => "$less"
  | Leqn     => "$lesseq"
  | Greatern => "$greater"
  | Geqn     => "$greatereq"
  | Plusi    => "$sum"
  | Minusi   => "$difference"   
  | Multi    => "$product"
  | Lessi    => "$less"
  | Leqi     => "$lesseq"
  | Greateri => "$greater"
  | Geqi     => "$greatereq"
  | Negated  => "$uminus"
  | Othercomb => raise DATATYPE_ERR "op_symb" "not an tff operator"


datatype STRUCTLEAFC = True | False | Otherleafc

fun structleafc term =
  switcharg term
    [
    (equal T ,True),
    (equal F ,False)
    ]
    Otherleafc

(* Reader *)  
fun is_tfffunctor tffvar =
  is_member tffvar 
  [ "$sum",
    "$difference",   
    "$product",
    "$less",
    "$lesseq",
    "$greater",
    "$greatereq",
    "$uminus"]

fun read_tfffunctor tffvar =
  case tffvar of
    "$sum"        => intSyntax.plus_tm
  | "$difference" => intSyntax.minus_tm   
  | "$product"    => intSyntax.mult_tm
  | "$less"       => intSyntax.less_tm
  | "$lesseq"     => intSyntax.leq_tm
  | "$greater"    => intSyntax.great_tm
  | "$greatereq"  => intSyntax.geq_tm
  |  "$uminus"    => intSyntax.negate_tm
  | _  => raise DATATYPE_ERR "read_tfffunctor" tffvar

fun is_tfftruefalse tffvar =
  is_member tffvar ["$true","$$true","$false","$$false"]
  
fun read_tfftruefalse tffvar =
  case tffvar of
    "$true"   => T
  | "$$true"  => T   
  | "$false"  => F
  | "$$false" => F
  | _  => raise DATATYPE_ERR "read_tfftruefalse" tffvar






end

