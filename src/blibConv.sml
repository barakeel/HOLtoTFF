structure blibConv :> blibConv =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype 
     blibSyntax blibBconv blibBrule blibBtactic
     blibExtractvar blibFreshvar blibExtracttype 
     blibNamevar blibHO 

fun CONV_ERR function message =
  HOL_ERR{origin_structure = "blibConv",
	        origin_function = function,
          message = message}


(* no lambda - abstraction *)
(* Should remove exists unique and cond on boolean first *)

(* LAMBDA-LIFTING *)
thislambda-abstraction  <=>  freshvar + creation of new term at the top


(* BOOL CONV *)

UNBETA_CONV subterm term

list_mk_abs (get_bvl abs, abs) = g
ONCE_REWRITE_CONV 
val term = ``!A f. A(f:bool) = (((f:bool) ==> A(T)) /\ (((~f) ==> A(F))))``  ;

(* test
val term = ``!z. P (\x . x + z:num) : bool``;
val term = ``P (\x . x + z:num) : bool``;
val abs = ``\x . x + z``;
FUN_CONV_sub abs term;
fun_axiom term;
*)

val thm = ASSUME term;
val term = ``(\x:bool. B x) (!y. y:num = 0):bool``;
REWR_CONV thm term;
(* Problem is abstraction containing free variable *)

val term = ``A(Abs) <=>  f(fv) = Abs /\ A(f(fv)) ``  ;
val thm = ASSUME term

(* 
1 find interesting subterm
2 abstract over it
3 use the rewrite rule
4 repeat the process
*)
exception Not_found
(* find *)
fun find_abs term =
  if is_var term then raise Not_found
  else if is_const term then raise Not_found
  else if is_forall term then find_abs (snd (strip_forall term))
  else if is_exists term then find_abs (snd (strip_exists term))
  else if is_comb term then 
    find_abs (rator term) handle Not_found => find_abs (rand term)
  else if is_abs term then term
  else raise Not_found
  
fun abs_to_subst term abs = 
  let val fvl = free_vars abs in
  let val newabs = list_mk_abs (fvl,abs) in
  let val var = mk_var ("abs", type_of newabs) in
    [abs |-> list_mk_comb (var,fvl)]
  end end end

val newterm = mk_conj (newdef, rebuild_atoml map subst s atoml);

(* same for booleans *)

(* test 
val term = ``P (\x. x + 1) (\y.y) /\ !x. Q (\z. z + x)``;
val term = ``P (\x z. x + z):bool``;
val term = ``P (\x. (x = \z.z) ):bool`` ;
FUN_CONV term;
find_free_abs term ;
*)

(* APP CONV *)   
fun app_axiom appname term =
  let val (oper,arg) = dest_comb term in
  let val opty = type_of oper in
  let val app = mk_var (appname,mk_type ("fun",[opty,opty])) in
    mk_thm ([],mk_eq (term, list_mk_comb (app,[oper,arg])))
  end end end
 
(* test
show_assums :=  true;
val term = ``f a b c``;
val appname = "App";
*)

(* lowestarity *)
fun get_la termal (term,arity) =
  case termal of
    [] => arity
  | (t,a) :: m => if term = t andalso a < arity 
                  then get_la m (term,a) 
                  else get_la m (term,arity) 
   
fun collapse_la varal = map (get_la varal) varal

fun get_fvclal terml =
  let val fvclal1 = collapse_la (merge (map get_fvcal terml)) in
  let val tyl = map type_of (get_bvl_goal terml) in
  let fun change_arity tyl (fvc,a)  =
    if is_member (type_of fvc) tyl then (fvc,0) else (fvc,a)
  in
    map (change_arity tyl) fvclal1
  end end end

fun app_conv_sub name la a term =
   if lowa = a then raise UNCHANGED
   else if lowa < a then 
     (RATOR_CONV (app_conv_sub name la (a -1)) THENC app_axiom name) term
   else raise CONV_ERR "app_conv_sub" "lowest arity > arity"
   
fun app_conv name fvclal bvl term = 
  if is_comb term then 
    if is_binop term then BINOP_CONV (app_conv name fvclal bvl) term else
    if is_neg term then RAND_CONV (app_conv name fvclal bvl) term else 
    if is_quant term then 
      let val (qbvl,_) = strip_quant term in
        STRIP_QUANT_CONV (app_conv name fvclal (qbvl @ bvl)) term
      end
    else  
      let val (oper,_) = strip_comb term in
      let val a = get_arity term in
      let val la = if is_member oper bvl then 0 else lookup oper fvclal in
        (ARG_CONV (app_conv name fvclal bvl) THENC app_conv_sub name la a) term 
      end end end
  else raise UNCHANGED
  
fun APP_CONV appname terml term = 
  app_conv appname (get_fvclal2 terml) [] term
      
(* test
show_assums :=  true;
val subterm = ``f a b ``;
val appname = "App";
val term = ``(f a b = 2) /\ (f = g)``;
*)

(* BOOL_BV_CONV *)
fun BOOL_BV_CONV_sub term =
  let val var = fst (dest_forall term) in
    if not (type_of var = bool) then raise UNCHANGED else
  let val th11 = ASSUME term in
  let val t2 = concl (CONJ (SPEC F th11) (SPEC T th11)) in
    mk_thm ([],mk_eq (term,t2))
  end end end
  
fun BOOL_BV_CONV term =
  if not (is_forall term) then raise UNCHANGED else 
    (QUANT_CONV BOOL_BV_CONV THENC BOOL_BV_CONV_sub) term

(* test 
val term = ``!x:bool y:num z:bool. x /\ (y = 0) /\ z``;     
*)

end
