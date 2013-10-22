structure blibNumconv (*:> blibNumconv*) =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype 
     blibSyntax blibBrule blibBtactic
     blibExtractvar blibExtracttype blibFreshvar


fun NUMCONV_ERR function message =
  HOL_ERR{origin_structure = "blibNumconv",
          origin_function = function,
          message = message}

(* NUMERAL TO INTEGER TRANSLATION *)
(* global references *)
val fdefdict:(term * term) list ref = ref []	
val used: term list ref = ref []


(* preprocessing *)
fun ORIENT_NUM_INEQ_CONV term =
  (
  REWRITE_CONV [SPEC_ALL arithmeticTheory.GREATER_EQ]
  THENC
  REWRITE_CONV [SPEC_ALL arithmeticTheory.GREATER_DEF] 
  )
  term

fun ORIENT_NUM_INEQ_TAC goal = CONV_HYP_TAC ORIENT_NUM_INEQ_CONV goal


(* test
val term = ``!x. x:num>0 /\ y:num>=0``;
*)

(* definitions *)   
fun mk_funtype argtyl imty =
  case argtyl of
    [] => imty
  | ty :: m => mk_type("fun",[ty,mk_funtype m imty])

fun type_num_to_int ty = 
  if ty = ``:num`` then ``:int`` else ty

fun inject_num arg =
  if has_numty arg 
  then mk_comb (intSyntax.int_injection,arg)
  else arg

fun inj_fun_def term =
  let val (op1,argl) = strip_comb term in
    if is_member op1 (map fst (!fdefdict)) then lookup op1 (!fdefdict)
    else 
      let val argtyl1 = map type_of argl in 
      let val namel = mk_newnamel "x" (length argl) (map name_of (!used)) in  
      let val argl1 = mk_newvarl (mk_varl (namel,argtyl1)) (!used) in
      let val t1 = if has_numty term 
                   then mk_comb 
                        (intSyntax.int_injection,list_mk_comb (op1,argl1)) 
                   else list_mk_comb (op1,argl1)
      in
      let val argtyl2 = map type_num_to_int argtyl1 in
      let val opty2 = mk_funtype argtyl2 (type_num_to_int (type_of term)) in
      let val op2 = mk_newvar (mk_var (name_of op1, opty2)) (!used) in
      let val argl2 = (map inject_num argl1) in
      let val t2 = list_mk_comb (op2,argl2) in
      let val t3 = list_mk_forall (argl1, mk_eq (t2,t1)) in
        (
        used := op2 :: (!used);
        used := argl1 @ argl2 @ (!used);
        fdefdict := (op1,t3) :: (!fdefdict);
        t3
        )
      end end end end end
      end end end end end
  end

(* test
val used: term list ref = ref [];
val term = ``P (f (x:num):num) (y:int):bool``;
(!fdefdict);
*)

(* replace all numeral type by an integer type *)
fun INTF_CONV_SUB term =
  if is_leaf term then raise UNCHANGED
  else
  if rator term = intSyntax.int_injection
  then
    let val t = rand term in
    if is_leaf t then raise UNCHANGED      
    else
      case termarith t of
        Plusn => let val (t1,t2) = numSyntax.dest_plus t in
                  SYM (SPECL [t1,t2] integerTheory.INT_ADD)
                end
      | Minusn => let val (t1,t2) = numSyntax.dest_minus t in
                   SPECL [t1,t2] int_arithTheory.INT_NUM_SUB
                 end
      | Multn => let val (t1,t2) = numSyntax.dest_mult t in
                  SYM (SPECL [t1,t2] integerTheory.INT_MUL)
                end
      | _ => let val (_,argl) = strip_comb t in 
             let val def = inj_fun_def t in
               SYM (SPECL argl (ASSUME def))
             end end
    end
  else if is_connector term then raise UNCHANGED
  else if is_eq term 
  then
    if has_numty (lhs term)
    then
      let val (t1,t2) = dest_eq term in
        SYM (SPECL [t1,t2] integerTheory.INT_INJ)    
      end
    else raise UNCHANGED  
  else if is_intarith term 
  then raise UNCHANGED
  else       
    case termarith term of      
        Lessn => let val (t1,t2) = numSyntax.dest_less term in
                 SYM (SPECL [t1,t2] integerTheory.INT_LE) 
                end
      | Leqn => let val (t1,t2) = numSyntax.dest_leq term in
                SYM (SPECL [t1,t2] integerTheory.INT_LT)
               end
      | _ => let val (operator,argl) = strip_comb term in
             let val def = inj_fun_def term in
               SYM (SPECL argl (ASSUME def))
             end end

fun ARG_CONV conv term =
  if is_comb term 
  then (RAND_CONV conv THENC RATOR_CONV (ARG_CONV conv)) term
  else raise UNCHANGED 
      
fun INTF_CONV_aux term =
  if is_leaf term orelse
     (rator term = intSyntax.int_injection andalso is_leaf (rand term)) 
  then raise UNCHANGED
  else
    let val eqth1 = QCONV INTF_CONV_SUB term in
    let val rht = rhs (concl eqth1) in
      if rator rht = intSyntax.int_injection
      then
        let val eqth2 = 
          QCONV (RAND_CONV (ARG_CONV INTF_CONV_aux)) rht 
        in
          TRANS eqth1 eqth2
        end
      else
        let val eqth2 = QCONV (ARG_CONV INTF_CONV_aux) rht in
          TRANS eqth1 eqth2
        end  
    end end
  
      
fun INTF_CONV term = STRIP_QUANT_CONV INTF_CONV_aux term  


fun intf_one hyp1 goal =
  let val eqthm = QCONV INTF_CONV hyp1 in
  let val nothyp1 = remove hyp1 (fst goal) in
  let val hyp2 = (rhs o concl) eqthm in
  let val defl = hyp eqthm in
    ((hyp2 :: defl) @ nothyp1,snd goal)
  end end end end


(* problem

val hyp1 = hd (fst goal);
val finalgoal = intf_one hyp1 goal;
*)

(* tools *)
fun num_to_int var = 
  if has_numty var 
  then mk_var (name_of var,``:int``)
  else var

fun mk_couplel l1 l2 =
  if not (length l1 = length l2) then raise NUMCONV_ERR "mk_couplel" ""
  else if null l1 then []
  else (hd l1,hd l2) :: mk_couplel (tl l1) (tl l2) 

fun coerc_couple (v1,v2) =
  if type_of v1 = ``:num`` andalso
     type_of v2 = ``:int``
  then 
    (v1,mk_comb (intSyntax.Num_tm,v2))
  else (v1,v2)

fun is_inject term =
  if is_comb term then
    rator term = intSyntax.int_injection
  else
    false

fun dest_inject term = 
  if is_inject term then rand term
  else raise NUMCONV_ERR "dest_inject" ""
 
(* 
val intdef = hd (hyp lemma1);
val intdef = hd (tl (hyp lemma1));
val thm = th1;
 *)
 
fun remove_intdef intdef thm =
  let val (bvl,t) = strip_forall intdef in
  (* should use newvar or something to prevent clashes *)
  let val bvli = map num_to_int bvl in
  let val bvlcoerc = map snd (map coerc_couple (mk_couplel bvl bvli)) in
  let val (f1,_) = strip_comb (lhs t) in
  let val th1 = DISCH intdef thm in
  let val th2 = GEN f1 th1 in
    if is_inject (rhs t)
    then
      let val (f2,_) = strip_comb (dest_inject (rhs t)) in
      let val t1 =
        mk_comb (intSyntax.int_injection, list_mk_comb (f2,bvlcoerc))
      in
      let val lambdaf = list_mk_abs (bvli,t1) in
      let val th3 = SPEC lambdaf th2 in
      let val eqth4 = REDEPTH_CONV BETA_CONV (concl th3) in
      let val th5 = EQ_MP (eqth4) th3 in
      let val lemma = SPEC_ALL integerTheory.NUM_OF_INT in
      let val eqth6 = REWRITE_CONV [lemma] (concl th5) in
      let val th7 = EQ_MP eqth6 th5 in
        th7
      end end end end end
      end end end end    
    else
      let val (f2,_) = strip_comb (rhs t) in
      let val t1 = list_mk_comb (f2,bvlcoerc) in
      let val lambdaf = list_mk_abs (bvli,t1) in
      let val th3 = SPEC lambdaf th2 in
      let val eqth4 = REDEPTH_CONV BETA_CONV (concl th3) in
      let val th5 = EQ_MP (eqth4) th3 in
      let val lemma = SPEC_ALL integerTheory.NUM_OF_INT in
      let val eqth6 = REWRITE_CONV [lemma] (concl th5) in
      let val th7 = EQ_MP eqth6 th5 in
        th7
      end end end end end
      end end end end  
  end end end end end 
  end

fun remove_intdefl intdefl thm = repeatchange remove_intdef intdefl thm

fun intf_one_val hyp1 goal thm =
  let val lemma1 = QCONV INTF_CONV hyp1 in
  let val intdefl = hyp lemma1 in
  let val (lemma2,_) = EQ_IMP_RULE lemma1 in 
  let val th1 = PROVE_HYP (UNDISCH lemma2) thm in
  let val th2 = remove_intdefl intdefl th1 in
    th2
  end end end end end
  
fun INTF_ONE_TAC hyp1 goal =
  mk_tac1 (intf_one hyp1) (intf_one_val hyp1) goal
  
fun INTF_TAC_aux hypl goal =
  case hypl of
    [] => ALL_TAC goal
  | hyp1 :: m =>  ((INTF_ONE_TAC hyp1) THEN
                  (INTF_TAC_aux m))
                  goal  

fun INTF_TAC goal = INTF_TAC_aux (fst goal) goal
(* test      
show_assums := true;
val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (x:num)``;
val term2 = ``(x:num) + (z:num) = (0:num)``;
val goal = ([term1,term2],F);

val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (x:num)``;
val term2 = ``!z:num (y:num). (&z) = ((&(h y:num)):int)``;
val goal = ([term1,term2],F);

val hyp1 = hd (fst goal);
val hyp1 = hd (tl (fst goal));

snd (INTF_ONE_TAC hyp1 goal);
INTF_TAC (fst goal)  goal;

val finalgoal = intf_one hyp1 goal;
val thm = mk_thm finalgoal;
val newthm = intf_one_val hyp1 goal thm;
val intdef = hd intdefl;
val th2 = remove_intdef intdefl thm;
*)

(* remove all &(intSyntax.int_injection) operator on variables*)
fun NUM_INT_FORALL_CONV_FST term =   
  let val (var,t) = dest_forall term in
    if type_of var = ``:num``
    then
      let val th1 = int_arithTheory.INT_NUM_FORALL in
      let val newvar = mk_newvar (mk_var ("y",``:int``)) (!used) in
      let val t1 = mk_comb (intSyntax.int_injection,var) in
      let val s = [t1 |-> newvar] in
      let val preabs = subst s t in
      let val abs = mk_abs (newvar,preabs) in
      let val p = mk_var ("P",``:int -> bool``) in
      let val equality = mk_eq (p,abs) in
      let val eqthm1 = ASSUME equality in
      let val newthm = SUBS [eqthm1] int_arithTheory.INT_NUM_FORALL in
      let val eqthm2 = REDEPTH_CONV BETA_CONV (concl newthm) in
      let val th2 = EQ_MP eqthm2 newthm in
        (
        used := newvar :: (!used);
        remove_unused_def (hd (hyp th2)) th2
        )
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

fun intv_def term = 
  let val v0 = mk_var (name_of (rand term),``:int``) in
  let val v1 = mk_newvar v0 (!used) in
    (used := v1 :: (!used);
     mk_eq (v1,term))
  end end
 
local fun test term t = 
  if not (free_in t term) then false 
  else if not (is_comb t) then false
  else if not (rator t = intSyntax.int_injection) then false
  else if not (is_var (rand t) orelse is_const (rand t)) then false
  else if numSyntax.is_numeral (rand t) then false
  else true 
in 
fun intv_conv term = 
  let val terml = find_terms (test term) term in
  let val thml = map (SYM o ASSUME) (map intv_def terml) in
    REWRITE_CONV thml term
  end end
end

fun INTV_CONV term =
  (intv_conv THENC NUM_INT_FORALL_CONV THENC normalForms.CNF_CONV) term

(*
show_assums:=true;

val term = ``∀x. (&(x:num):int) + 2 * (&(y:num):int) + (&(z:num):int) = 0``;
val hyp1 = term;
val goal = ([term],F);
val thm = mk_thm (remove_int_injection hyp1 goal);

val intvdef = hd (tl (hyp th1));
val thm = th1;
*)

fun remove_intvdef intvdef thm =
  let val th1 = DISCH intvdef thm in
  let val th2 = GEN (lhs intvdef) th1 in
  let val th3 = SPEC (rhs intvdef) th2 in
  let val eqth4 = normalForms.CNF_CONV (concl th3) in 
  let val th5 = EQ_MP eqth4 th3 in
    th5
 end end end end end

fun remove_intvdefl intvdefl thm = repeatchange remove_intvdef intvdefl thm

fun intv_one hyp1 goal =
  let val lemma1 = QCONV INTV_CONV hyp1 in
  let val nothyp1 = remove hyp1 (fst goal) in
  let val hyp2 = (rhs o concl) lemma1 in
  let val defl = hyp lemma1 in
    ((hyp2 :: defl) @ nothyp1,snd goal)
  end end end end

fun intv_one_val hyp1 goal thm =
  let val lemma1 = QCONV INTV_CONV hyp1 in
  let val intvdefl = hyp lemma1 in
  let val (lemma2,_) = EQ_IMP_RULE lemma1 in 
  let val th1 = PROVE_HYP (UNDISCH lemma2) thm in
  let val th2 = remove_intvdefl intvdefl th1 in
    th2
  end end end end end 

fun INTV_ONE_TAC hyp1 goal =
  mk_tac1 (intv_one hyp1) (intv_one_val hyp1) goal

fun INTV_TAC_aux hypl goal =
  case hypl of
    [] => ALL_TAC goal
  | hyp1 :: m =>  ((INTV_ONE_TAC hyp1) THEN
                  (INTV_TAC_aux m))
                  goal  

fun INTV_TAC goal = INTV_TAC_aux (fst goal) goal


 
(* test 
val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (r:num)``;
val term2 = ``(x:num) + (z:num) = (0:num)``;
val goal = ([term1,term2],F);

val newgoal = hd (fst(INTF_TAC goal));
val t1 = list_nth 0 (fst newgoal);
val t2 = list_nth 1 (fst newgoal);
val goal = ([t1,t2],F);

val newgoal = hd (fst(INTV_TAC goal));
val thm = mk_thm (intv_injection_one t2 goal);

*)

fun intf_test extdef =
  let val (bvl,eqt) = strip_forall extdef in
  let val t2 = rhs eqt in
  let val (oper,arg) = dest_comb t2 in
    oper = intSyntax.int_injection
  end end end

fun intf_axiom extdef =
  let val (bvl,eqt) = strip_forall extdef in
  let val (_,arg) = dest_comb (rhs eqt) in
  let val th1 = ASSUME extdef in
  let val axiom1 = integerTheory.INT_POS in
  let val th2 = SPEC arg axiom1 in
  let val th3 = GENL bvl (SUBS [SYM (SPEC_ALL th1)] th2) in
  let val th4 = (QCONV (NUM_INT_FORALL_CONV THENC normalForms.CNF_CONV))
                (concl th3) 
  in
  let val th5 = EQ_MP th4 th3 in
      th5
  end end end end end end end end

fun num_int_aux term =
  let val eqth1 = (QCONV (ORIENT_NUM_INEQ_CONV THENC INTF_CONV)) term in
  let val revextdefl = hyp eqth1 in
  let val axioml = map intf_axiom revextdefl in
  let val t1 = rhs (concl eqth1) in
  let val eqth2 = (QCONV INTV_CONV) t1 in  
  let val t2 = rhs (concl eqth2) in
    t2 :: map concl axioml
  end end end end end end


(*
val thml = filter intf_test (map snd (!fdefdict));
fun NUM_INT_TAC goal =
   (
   used := all_var_goal goal;
   (ORIENT_NUM_INEQ_TAC THEN INTF_TAC THEN INTV_TAC) goal
   )
   
 
 
 *)
  
 (* 
 show_assums := true;
 val goal = ([``!x.x + 2 = (0: int)``, ``(g (f (x:num):num) = (2:num))``],F); 
 val goal = ([ ``g (f (x:num):num):bool``],F); 


 val goal1 = hd (fst (ORIENT_NUM_INEQ_TAC goal));
 val goal2 = hd (fst (INTF_TAC goal1));
*)


(* test 
show_assums:=true;
val revextdef = ``∀x x1. (& (f x x1)) = (f' (&x) x1 : int)``;
*)

(* NUMERAL TO NUMERAL CONVERSION *)
(* find *)
local fun is_interesting_in term subterm = 
  has_numty subterm andalso 
  free_in subterm term andalso 
  not (numSyntax.is_numeral subterm) andalso
  is_var subterm
in
fun find_free_num term = 
  erase_double_aconv (filter (is_interesting_in term) (all_fosubterm term))
end 
  
(* term should start with a quantifier *)  
local fun is_interesting_in term subterm = 
  bound_by_quant subterm term andalso
  has_numty subterm andalso 
  not (numSyntax.is_numeral subterm) andalso
  is_var subterm
in 
fun find_bound_num term =  
  erase_double_aconv (filter (is_interesting_in term) (all_fosubterm term))
end  
(* end find *)

fun num_axiom term = 
  let val axiom = arithmeticTheory.ZERO_LESS_EQ in
    SPEC term axiom
  end

(* term should have of type bool *)
fun num_conv_conj subterml term =
  let val axioml = map num_axiom subterml in
    if null axioml then raise UNCHANGED
    else   
      let val axiom = LIST_CONJ axioml in
      (* first part *)
      let val th11 = ASSUME term in
      let val th12 = CONJ axiom th11 in  
      let val th13 = DISCH term th12 in  
      (* second part *) 
      let val th21 = ASSUME (concl th12) in
      let val th22 = CONJUNCT2 th21 in
      let val th23 = DISCH (concl th12) th22 in
        (* together *)
        IMP_ANTISYM_RULE th13 th23
      end end end end end end end
  end

(* test
val term = ``(0 < y) /\ (x = 0) /\ (?x:num . (y:num) = (y:num))``;
val subterml = find_free_num term;
show_assums := true;
*)  
fun num_conv_imp subterml term =
  let val axioml = map num_axiom subterml in
    if null axioml then raise UNCHANGED
    else   
      let val axiom = LIST_CONJ axioml in
      (* first part *)
      let val th11 = ASSUME term in
      let val th12 = DISCH (concl axiom) th11 in  
      let val th13 = DISCH term th12 in  
      (* second part *) 
      let val th21 = ASSUME (concl th12) in
      let val th22 = UNDISCH th21 in
      let val th23 = PROVE_HYP axiom th22 in
      let val th24 = DISCH (concl th12) th23 in
      (* together *) 
        IMP_ANTISYM_RULE th13 th24
      end end end end end end end end
  end

fun num_conv_forall term =
  let val terml = find_bound_num term in
    STRIP_QUANT_CONV (num_conv_imp terml) term  
  end

fun num_conv_exists term =
  let val terml = find_bound_num term in
    STRIP_QUANT_CONV (num_conv_conj terml) term  
  end 

(* test 
val term = ``!x y. A ==> (x + y + z = f x)``;
val term = ``?x y. (x = 0) /\ (y = 0) /\ (z = 0) /\ (f (y:num) = 0)``;
*)

fun num_conv_aux term =   
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Integer => raise UNCHANGED
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connector term of
      Forall => (num_conv_forall THENC (STRIP_QUANT_CONV num_conv_aux)) term
    | Exists => (num_conv_exists THENC (STRIP_QUANT_CONV num_conv_aux)) term        
    | _ => COMB_CONV num_conv_aux term
    )
  | Abs => raise NUMCONV_ERR "num_conv" "abstraction"

fun num_conv term =
  let val terml = find_free_num term in
    (num_conv_aux THENC (num_conv_conj terml)) term
  end
  
(* test
val term = ``(a = 0) /\ ?x y. (x = 0) /\ (!x. x + 1 = z) /\ (f y = 0)``;
*)
fun numf_axiom_w (f,arity) = 
  let val (argl,image) = strip_type_n (type_of f,arity) in
  let val argtyl = map fst argl in
  let val imagety = fst image in
    if imagety = ``:num``
    then 
      let val namel = mk_newnamel "x" (length argl) [name_of f] in   
      let val varl = mk_varl (namel,argtyl) in
      let val newvarl = mk_newvarl varl (all_var f) in
      let val numvarl = filter has_numty varl in
      let val axiomvar = if null numvarl then ASSUME T
                    else LIST_CONJ (map num_axiom numvarl) 
      in
      let val term = list_mk_comb (f,newvarl) in
      let val axiom = num_axiom term in
      let val th1 = 
        if null numvarl then axiom
        else DISCH (concl axiomvar) (ADD_ASSUM (concl axiomvar) axiom)
      in 
      let val th2 = GENL varl th1 in
        EQ_MP (QCONV normalForms.CNF_CONV (concl th2)) th2
      end end end end end
      end end end end
    else raise NUMCONV_ERR "numf_axiom" "not a num type"
  end end end
fun numf_axiom (f,arity) = wrap "conv" "numf_axiom" "" numf_axiom_w (f,arity) 








(* test
val f = ``f : 'a -> num ``; 
val arity = 1; 
  normalForms.CNF_CONV (concl it);
*)


end