structure blibConv :> blibConv =
struct

open HolKernel Abbrev boolLib blibTools blibExtract 

exception Not_found

(* Lambda-abstraction and boolean rewrite *)
local fun find_ab term =
  if is_var term then 
    if type_of term = bool then term else raise Not_found
  else if is_const term then 
    if type_of term = bool andalso term <> T andalso term <> F 
    then term 
    else raise Not_found
  else if is_comb term then 
    if type_of term = bool then term
    else (find_ab (rator term) handle Not_found => find_ab (rand term))
  else if is_abs term then term
  else raise Not_found
in
fun find_absbool atom =
  if is_var atom orelse is_const atom then raise Not_found
  else if is_comb atom then
    (find_ab (rator atom) handle Not_found => find_ab (rand atom))
  else raise Not_found
end

fun abs_subst abs term = 
  let val fvl = free_vars abs in
  let val v = genvar (type_of (list_mk_abs (fvl,abs))) in
    (fvl,abs |-> list_mk_comb (v,fvl))
  end end

fun tryl f l =
  case l of 
    [] => raise Not_found
  | a :: m => ((a, f a) handle _ => tryl f m)

fun rw_absbool term =
  let val atoml = find_atoml term in
  let val (atom,ab) = tryl find_absbool atoml in
    if is_abs ab then
      let val (fvl,s) = abs_subst ab term in
      let val t0 = subst [s] atom in
      let val (bvl,t1) = strip_abs ab in
      let val t2 = list_mk_comb ((#residue s),bvl) in
      let val t3 = mk_conj (t0, list_mk_forall ((fvl @ bvl),mk_eq (t2,t1))) in
      let val thm = mk_thm ([], mk_eq (atom,t3)) in  
        (rhs o concl) (PURE_ONCE_REWRITE_CONV [thm] term)
      end end end end end end
    else (* it's a boolean *)
      let val (t1,t2) = (subst [ab |-> T] atom, subst [ab |-> F] atom) in
      let val t3 = mk_conj (mk_disj (mk_neg ab, t1), mk_disj (ab,t2)) in
      let val thm = mk_thm ([], mk_eq (atom,t3)) in  
        (rhs o concl) (PURE_ONCE_REWRITE_CONV [thm] term)
      end end end
  end end

(* test 
val term = ``P (\x. x (y:bool)) (\y.y) /\ !x. Q (\z. z + x)``;
*)

(* APP CONV *)
(* lowestarity *)
fun get_lal term =
  let val fvcal = get_fvcal term in
  let fun less (_,a) (_,b) = a < b in 
    sort less fvcal 
  end end

(* local conversion *)
fun app_axiom name term =
  let val (oper,arg) = dest_comb term in
  let val opty = type_of oper in
  let val app = mk_var (name,mk_type ("fun",[opty,opty])) in
    mk_thm ([],mk_eq (term, list_mk_comb (app,[oper,arg])))
  end end end

fun app_conv_sub name la a term =
   if la = a then raise UNCHANGED
   else if la < a then 
     (RATOR_CONV (app_conv_sub name la (a -1)) THENC app_axiom name) term
   else raise B_ERR "app_conv_sub" "lowest arity > arity"

(* global conversion *) 
fun ARG_CONV conv term =
  if is_comb term 
  then ((RAND_CONV conv) THENC (RATOR_CONV (ARG_CONV conv))) term 
  else raise UNCHANGED  

fun app_conv name lal bvl term = 
  if is_comb term then 
    if is_binop term orelse is_eq term orelse is_bina term then 
       BINOP_CONV (app_conv name lal bvl) term else
    if is_unop term orelse is_una term then RAND_CONV (app_conv name lal bvl) term else 
    if is_quant term then 
      let val (qbvl,_) = strip_quant term in
        STRIP_QUANT_CONV (app_conv name lal (qbvl @ bvl)) term
      end
    else  
      let val (oper,argl) = strip_comb term in
      let val a = length argl in
      let val la = if mem oper bvl then 0 else assoc oper lal in
        (ARG_CONV (app_conv name lal bvl) THENC app_conv_sub name la a) term 
      end end end
  else raise UNCHANGED
  
fun APP_CONV term = 
  let val name = new_name "App" (map (fst o dest_var) (get_bvl term @ free_vars term)) in
    app_conv name (get_lal term) [] term
  end 

(* val term = ``(f a b = 2) /\ (f a = g)``;*)
(* BOOL_BV_CONV *) (* should be done just before printing *)
fun BOOL_BV_CONV_sub term =
  let val var = fst (dest_forall term) in
    if not (type_of var = bool) then raise UNCHANGED 
    else
      let val th11 = ASSUME term in
      let val t2 = concl (CONJ (SPEC F th11) (SPEC T th11)) in
        mk_thm ([],mk_eq (term,t2))
      end end
  end
  
fun BOOL_BV_CONV term =
  if not (is_forall term) then raise UNCHANGED 
  else (QUANT_CONV BOOL_BV_CONV THENC BOOL_BV_CONV_sub) term

(* val term = ``!x:bool y:num z:bool. x \/ (y = 0) \/ z``*)
end
