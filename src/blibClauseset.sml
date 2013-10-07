structure blibClauseset (*:> blibClauseset*) =
struct

open HolKernel Abbrev boolLib 
     numSyntax intSyntax int_arithTheory arithmeticTheory integerTheory
     blibBtools blibDatatype 
     blibSyntax blibBrule 
     blibExtractvar blibExtracttype blibFreshvar

(* FORALL_CONJUNCTS_CONV *)
fun forall_conjuncts_conv_w term = 
  let val (bvl,t) = strip_forall term in
  (* first part *)
  let val th10 = ASSUME term in
  let val th11 = SPECL bvl th10 in
  let val thl12 = CONJUNCTS th11 in
  let val thl13 = map (GENL bvl) thl12 in
  let val th14 = LIST_CONJ thl13 in
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th20 = ASSUME (concl th14) in
  let val th21 = ASSUME t in
  let val th22 = strip_conj_hyp_rule th21 in
  let val thl23 = CONJUNCTS th20 in
  let val thl24 = map (SPECL bvl) thl23 in
  let val th25 = list_PROVE_HYP thl24 th22 in
  let val th26 = GENL bvl th25 in 
  let val th27 = DISCH (concl th14) th26 in
  (* together *)
    IMP_ANTISYM_RULE th15 th27
  end end end end end 
  end end end end end 
  end end end end end
fun forall_conjuncts_conv term = 
  wrap "blibClauseset" "forall_conjuncts_conv" "" forall_conjuncts_conv_w term  
  
(* test
val term = `` !x y z. ((x = 0) /\ (y = 0)) /\ ((x = 0) /\ (z = 0))``; 
val thm = ASSUME term;
show_assums := true;
*)

(* BOOL_BV_CONV *)
fun bool_bv_conv_sub term =
  let val var = (hd o fst o strip_forall) term in
  if not (has_boolty var) then raise UNCHANGED
  else
    (* preparation *)  
  let val disj = SPEC var BOOL_CASES_AX in
  let val lemma = SPEC var (ASSUME term) in
  let val eqth1 = ASSUME (lhand (concl disj)) in
  let val eqth2 = ASSUME (rand (concl disj)) in
    (* first part *)
  let val th11 = ASSUME term in
  let val th12 = SPEC T th11 in
  let val th13 = SPEC F th11 in
  let val th14 = CONJ th12 th13 in
  let val th15 = DISCH term th14 in
    (* second part *)
  let val goalT = ([lhand(concl disj), concl th14],concl lemma) in
  let val (_,fnT) = SUBST_TAC [eqth1] goalT in  
  let val th20T = ASSUME (concl th14) in
  let val th21T = CONJUNCT1 th20T in
  let val th22T = fnT [th21T] in

  let val goalF = ([rand(concl disj), concl th14],concl lemma) in
  let val (_,fnF) = SUBST_TAC [eqth2] goalF in  
  let val th20F = ASSUME (concl th14) in
  let val th21F = CONJUNCT2 th20F in
  let val th22F = fnF [th21F] in
    (* disj cases *)
  let val th30 = DISJ_CASES disj th22T th22F in
  let val th31 = GEN var th30 in
  let val th32 = DISCH (concl th14) th31 in
  (* together *)
    IMP_ANTISYM_RULE th15 th32
  end end end end end 
  end end end end end
  end end end end end 
  end end end end end
  end end 
  end
  
fun bool_bv_conv term =
  if not (is_forall term) then raise UNCHANGED
  else 
    (QUANT_CONV bool_bv_conv THENC bool_bv_conv_sub) term
    
(* test 
val term = ``!x:bool y:num z:bool. x /\ (y = 0) /\ z``;     
*)

(* NUMERAL TO INTEGER TRANSLATION *)
(* preprocessing *)
fun ORIENT_NUM_INEQ_CONV term =
  (
  REWRITE_CONV [SPEC_ALL GREATER_OR_EQ]
  THENC
  REWRITE_CONV [SPEC_ALL GREATER_DEF] 
  )
  term

(* definitions *)   
fun mk_funtype argtyl imty =
  case argtyl of
    [] => imty
  | ty :: m => mk_type("fun",[ty,mk_funtype m imty])

fun type_num_to_int ty = 
  if ty = ``:num`` then ``:int`` else ty

fun num_to_int arg =
  if has_numty arg 
  then mk_comb (int_injection,arg)
  else arg

fun inj_fun_def term usedv =
  let val (op1,argl) = strip_comb term in
  let val argtyl1 = map type_of argl in 
  let val namel = mk_newnamel "x" (length argl) (map name_of usedv) in  
  let val argl1 = list_mk_var (namel,argtyl1) in
  let val t1 = if has_numty term 
               then mk_comb (int_injection,list_mk_comb (op1,argl1)) 
               else list_mk_comb (op1,argl1)
  in
  let val argtyl2 = map type_num_to_int argtyl1 in
  let val opty2 = mk_funtype argtyl2 (type_num_to_int (type_of term)) in
  let val op2 = mk_newvar (mk_var (name_of op1, opty2)) usedv in
  let val argl2 = map num_to_int argl1 in
  let val t2 = list_mk_comb (op2,argl2) in
    list_mk_forall (argl1, mk_eq (t1,t2))
  end end end end end
  end end end end end
  
(* test
val term = ``P (x:num) (y:bool):bool``;
val usedv = all_var term;
*)

(* replace all numeral type by an integer type *)
fun NUM_INT_FUN_CONV_SUB usedv term =
  if is_leaf term then raise UNCHANGED
  else
  if rator term = int_injection
  then
    let val t = rand term in
    if is_leaf t then raise UNCHANGED      
    else
      case nodeconst t of
        Plus => let val (t1,t2) = numSyntax.dest_plus t in
                  SYM (SPECL [t1,t2] INT_ADD)
                end
      | Minus => let val (t1,t2) = numSyntax.dest_minus t in
                   SPECL [t1,t2] INT_NUM_SUB
                 end
      | Mult => let val (t1,t2) = numSyntax.dest_mult t in
                  SYM (SPECL [t1,t2] INT_MUL)
                end
      | _ => let val (_,argl) = strip_comb t in 
             let val def = inj_fun_def t usedv in
               SPECL argl (ASSUME def)
             end end
    end
  else
    case nodeconst term of
        Eq => if has_numty (lhs term)
              then
                let val (t1,t2) = dest_eq term in
                  SYM (SPECL [t1,t2] INT_INJ)    
                end
              else raise UNCHANGED
      | Less => let val (t1,t2) = numSyntax.dest_less term in
                 SYM (SPECL [t1,t2] INT_LE) 
                end
      | Leq => let val (t1,t2) = numSyntax.dest_leq term in
                SYM (SPECL [t1,t2] INT_LT)
               end
      | _ => let val (operator,argl) = strip_comb term in
             let val def = inj_fun_def term usedv in
               SPECL argl (ASSUME def)
             end end

fun ARG_CONV conv term =
  if is_comb term 
  then (RAND_CONV conv THENC RATOR_CONV (ARG_CONV conv)) term
  else raise UNCHANGED 
      
fun NUM_INT_FUN_CONV_aux usedv term =
  if is_leaf term then raise UNCHANGED
  else
  ((NUM_INT_FUN_CONV_SUB usedv) THENC 
  (ARG_CONV (NUM_INT_FUN_CONV_aux usedv))) 
  term

fun NUM_INT_FUN_CONV usedv term = 
  STRIP_QUANT_CONV (NUM_INT_FUN_CONV_aux usedv) term  

fun num_int_fun goal =
  let val hypl = fst goal in
  let val thml = map (NUM_INT_FUN_CONV (all_var_goal goal)) hypl in
  let val newhypl = map (rhs o concl) thml in
  let val defl = List.concat (map hyp thml) in
    (defl @ newhypl,snd goal)
  end end end end
  

(* 
show_assums := true;
val t1 = ``!z:num. f z h = (0:num) + (x:num)``;
val t2 = ``(x:num) + (y:num) = 0``;
val term = ``(x:int) + (y:int) = 0``;
val usedv = all_var term;
val goal : goal = ([t1,t2],F);
val thm = NUM_INT_FUN_CONV (all_var term) term;
val revextdef = hd (hyp thm);
numfun_test revextdef;
numfun_axiom revextdef;

CONV_HYP_TAC
*)

(* remove all &(int_injection) operator *)
fun NUM_INT_FORALL_CONV_FST term =   
  let val (var,t) = dest_forall term in
    if type_of var = ``:num``
    then
      let val th1 = INT_NUM_FORALL in
      let val newvar = mk_newvar (mk_var ("y",``:int``)) (all_var term) in
      let val t1 = mk_comb (int_injection,var) in
      let val s = [t1 |-> newvar] in
      let val preabs = subst s t in
      let val abs = mk_abs (newvar,preabs) in
      let val p = mk_var ("P",``:int -> bool``) in
      let val equality = mk_eq (p,abs) in
      let val eqthm1 = ASSUME equality in
      let val newthm = SUBS [eqthm1] INT_NUM_FORALL in
      let val eqthm2 = REDEPTH_CONV BETA_CONV (concl newthm) in
      let val th2 = EQ_MP eqthm2 newthm in
        remove_unused_def (hd (hyp th2)) th2
      end end end end end 
      end end end end end 
      end end
    else raise UNCHANGED
  end
 
fun NUM_INT_FORALL_CONV term =
  if is_forall term 
  then 
    ((QUANT_CONV NUM_INT_FORALL_CONV) THENC NUM_INT_FORALL_CONV_FST)
      term  
  else 
    raise UNCHANGED 

fun intvar_def i term = 
  let val newi0 = mk_var (name_of (rand i),``:int``) in
  let val newi = mk_newvar newi0 (all_var term) in
    mk_eq (i,newi)
  end end
 
local fun test term t = 
  if not (free_in t term) then false 
  else if not (is_comb t) then false
  else if not (rator t = int_injection) then false
  else if not (is_var (rand t) orelse is_const (rand t)) then false
  else if is_numeral (rand t) then false
  else true 
in 
fun int_var_conv term = 
  let val varl = find_terms (test term) term in
  let val thml = map ASSUME (map (inv intvar_def term) varl) in
    REWRITE_CONV thml term
  end end
end

fun REMOVE_INT_INJECTION_CONV  term =
  (int_var_conv THENC NUM_INT_FORALL_CONV THENC normalForms.CNF_CONV) term

(*
val term = ``∀x. &x + 2 * &y + &z = 0``;
*)
fun numfun_test revextdef =
  let val (bvl,eqt) = strip_forall revextdef in
  let val t1 = lhs eqt in
  let val (oper,arg) = dest_comb t1 in
    oper = int_injection 
  end end end

fun numfun_axiom revextdef =
  let val (bvl,eqt) = strip_forall revextdef in
  let val (oper,arg) = dest_comb (lhs eqt) in
  let val th1 = ASSUME revextdef in
  let val eqth1 = (QCONV (STRIP_QUANT_CONV SYM_CONV)) revextdef in  
  let val th2 = EQ_MP eqth1 th1 in
  let val axiom1 = INT_POS in
  let val th3 = SPEC arg axiom1 in
  let val th4 = GENL bvl (SUBS [SYM (SPEC_ALL th2)] th3) in
  let val th5 = (QCONV (NUM_INT_FORALL_CONV THENC normalForms.CNF_CONV))
                (concl th4) 
  in
  let val th6 = EQ_MP th5 th4 in
      th6
  end end end end end end end end end end

fun num_int_aux usedv term =
  let val eqth1 = (QCONV (ORIENT_NUM_INEQ_CONV THENC NUM_INT_FUN_CONV usedv)) term in
  let val revextdefl = hyp eqth1 in
  let val axioml = map numfun_axiom revextdefl in
  let val t1 = rhs (concl eqth1) in
  let val eqth2 = (QCONV REMOVE_INT_INJECTION_CONV) t1 in  
  let val t2 = rhs (concl eqth2) in
    t2 :: map concl axioml
  end end end end end end

fun num_int goal =
  let val usedv = all_var_goal goal in
  let val hypl = fst goal in
  let val newhypl = List.concat (map (num_int_aux usedv) hypl) in
    (newhypl,snd goal)
  end end end
  
 (* 
 val goal = ([``!x.x + 2 = (0: num)``, ``g (f x:num):num``],F); 
 val goal = ([``!x.x + 2 = (0: int)``, ``g (f x:num):num``],F); 
 val term = ``!x.x + 2 = (0: int)``;
 val term =  ``g (f x:num):num``;

 val usedv = all_var term;
fun num_int_val =
fun NUM_INT_TAC =
*)


(* test 
show_assums:=true;
val revextdef = ``∀x x1. (& (f x x1)) = (f' (&x) x1 : int)``;
*)



end