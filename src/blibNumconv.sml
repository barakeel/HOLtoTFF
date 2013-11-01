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
val fdefdict:(term * thm) list ref = ref []	
val vdefdict:(term * term) list ref = ref []
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
fun mk_funtype (argtyl,imty) =
  case argtyl of
    [] => imty
  | ty :: m => mk_type("fun",[ty,mk_funtype (m,imty)])

fun type_num_to_int ty = 
  if ty = ``:num`` then ``:int`` else ty

fun inject_num arg =
  if has_numty arg 
  then mk_comb (intSyntax.int_injection,arg)
  else arg

fun mk_couplel l1 l2 =
  if not (length l1 = length l2) then raise NUMCONV_ERR "mk_couplel" ""
  else if null l1 then []
  else (hd l1,hd l2) :: mk_couplel (tl l1) (tl l2) 

fun coerc_int (v1,v2) =
  if type_of v1 = ``:num`` andalso
     type_of v2 = ``:int``
  then 
    mk_comb (intSyntax.Num_tm,v2)
  else v2
  
fun CONV_RULE conv thm = EQ_MP (conv (concl thm)) thm  
  
  
(* *)  
fun inj_fun_axiom term =
  let val (op1,argl) = strip_comb term in
    if is_member op1 (map fst (!fdefdict)) then lookup op1 (!fdefdict)
    else 
      let val tyl1 = map type_of argl in 
      let val namel = mk_list (length argl) "x" in  
      let val argl0 = mk_newvarl (mk_varl (namel,tyl1)) (!used) in
      let val argl1 = 
        mk_newvarl (mk_varl (namel,map type_num_to_int tyl1)) (!used) 
      in
      let val coercl = map coerc_int (mk_couplel argl argl1) in
      let val injectl = (map inject_num argl0) in
      (* def *)
      let val t1 = list_mk_comb (op1,coercl) in
      let val t2 = if has_numty term 
                   then mk_comb (intSyntax.int_injection,t1) 
                   else t1
      in
      let val t3 = list_mk_abs (argl1,t2) in
      let val tyl2 = map type_num_to_int tyl1 in
      let val imty2 = type_num_to_int (type_of term) in
      let val opty2 = mk_funtype (tyl2,imty2) in
      let val op2 = mk_newvar (mk_var (name_of op1, opty2)) (!used) in
      let val t4 = mk_eq (op2,t3) in
      (* axiom *)
      let val th1 = ASSUME t4 in 
      let val th2 = CONV_RULE (list_FUN_EQ_CONV argl1) th1 in
      let val th3 = SPECL injectl th2 in
      let val th4 = CONV_RULE (REDEPTH_CONV BETA_CONV) th3 in
      let val th5 = SPEC_ALL integerTheory.NUM_OF_INT in
      let val th6 = CONV_RULE (REWRITE_CONV [th5]) th4 in
      let val th7 = GENL argl0 th6 in 
        (
        used := op2 :: (!used);
        used := argl1 @ (!used);
        fdefdict := (op1,th7) :: (!fdefdict);
        th7
        )
      end end end end end 
      end end end end end 
      end end end end end 
      end end end end end end
end 



(* test
inj_fun_axiom term;
val used: term list ref = ref [];
val term = ``P (f (x:num):num) (y:int):bool``;
(!fdefdict);
*)

(* replace all numeral type by an integer type *)

fun is_inject term =
  if is_comb term then rator term = intSyntax.int_injection else false

fun INTF_CONV_SUB term =
  if is_leaf term then raise UNCHANGED
  else
  if is_inject term 
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
             let val th1 = inj_fun_axiom t in
               SYM (SPECL argl th1)
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
             let val th1 = inj_fun_axiom term in
               SYM (SPECL argl th1)
             end end

fun ARG_CONV conv term =
  if is_comb term 
  then (RAND_CONV conv THENC RATOR_CONV (ARG_CONV conv)) term
  else raise UNCHANGED 
      
fun INTF_CONV_aux term =
  if is_leaf term orelse
     (is_inject term andalso is_leaf (rand term)) 
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



fun INTF_ONE_TAC hyp1 goal =
  let val lemma1 = QCONV INTF_CONV hyp1 in
  let val defl = hyp lemma1 in
  let fun intf_one hyp1 goal =
    let val nothyp1 = remove hyp1 (fst goal) in
    let val hyp2 = (rhs o concl) lemma1 in
      ((hyp2 :: defl) @ nothyp1,snd goal)
    end end
  in
  let fun intf_one_val hyp1 goal thm =
    let val (lemma2,_) = EQ_IMP_RULE lemma1 in 
    let val th1 = PROVE_HYP (UNDISCH lemma2) thm in
    let val th2 = remove_defl defl th1 in
      th2
    end end end
  in
    mk_tac1 (intf_one hyp1) (intf_one_val hyp1) goal
  end end end end
   
fun INTF_TAC_aux hypl goal =
  case hypl of
    [] => ALL_TAC goal
  | hyp1 :: m =>  ((INTF_ONE_TAC hyp1) THEN
                  (INTF_TAC_aux m))
                  goal  

fun INTF_TAC goal = INTF_TAC_aux (fst goal) goal

(* test
val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (x:num)``;

val term2 = ``(x:num) + (z:num) = (0:num)``;
*)


fun mk_subt_abs (bv,subterm,term) =
   let val s = [subterm |-> bv] in
   let val t = subst s term in
     mk_abs (bv,t)
   end end   
     
(* remove all &(intSyntax.int_injection) operator on variables*)
fun intbv_conv_FST term =   
  let val (bv,t) = dest_forall term in
    if type_of bv = ``:num``
    then
      let val th1 = int_arithTheory.INT_NUM_FORALL in
      let val eqth2 = ((RAND_CONV (RENAME_VARS_CONV [name_of bv])) 
                      THENC (LAND_CONV (RENAME_VARS_CONV [name_of bv])))
                      (concl th1) 
      in
      let val th3 = EQ_MP eqth2 th1 in
      let val intbv = mk_var (name_of bv,``:int``) in
      let val t1 = mk_comb (intSyntax.int_injection,bv) in
      let val t2 = mk_subt_abs (intbv,t1,t) in
      let val t3 = mk_eq (mk_var ("P",``:int -> bool``),t2) in
      let val eqth4 = ASSUME t3 in
      let val th5 = SUBS [eqth4] th3 in
      let val eqth6 = REDEPTH_CONV BETA_CONV (concl th5) in
      let val th7 = EQ_MP eqth6 th5 in
        remove_def (hd (hyp th7)) th7
      end end end end end 
      end end end end end 
      end
    else raise UNCHANGED
  end
 
fun intbv_conv term =
  if is_forall term 
  then 
    ((QUANT_CONV intbv_conv) THENC intbv_conv_FST)
      term  
  else 
    raise UNCHANGED 

fun intfv_def term = 
  if is_member term (map fst (!vdefdict)) then lookup term (!vdefdict)
  else
    let val v1 = mk_var (name_of (rand term),``:int``) in 
    let val v2 = mk_newvar v1 (!used) in
      (used := v2 :: (!used);
       vdefdict := (term,mk_eq (v1,term)) :: (!vdefdict);
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
fun intfv_conv term = 
  let val terml = find_terms (test term) term in
  let val thml = map (SYM o ASSUME) (map intfv_def terml) in
    REWRITE_CONV thml term
  end end
end

fun INTV_CONV term =
  (intfv_conv THENC intbv_conv THENC normalForms.CNF_CONV) term


(*
val term = ``∀y. (&(y:num):int) + (&(z:num):int) = 0``;
val hyp1 = term;
val goal = ([term],F);
val thm = mk_thm (remove_int_injection hyp1 goal);
val intvdef = hd (tl (hyp th1));
val thm = th1;
*)

fun INTV_ONE_TAC hyp1 goal =
  let val lemma1 = QCONV INTV_CONV hyp1 in
  let val defl = hyp lemma1 in
  let fun intv_one hyp1 goal =
    let val nothyp1 = remove hyp1 (fst goal) in
    let val hyp2 = (rhs o concl) lemma1 in
      ((hyp2 :: defl) @ nothyp1,snd goal)
    end end
  in
  let fun intv_one_val hyp1 goal thm =
    let val (lemma2,_) = EQ_IMP_RULE lemma1 in 
    let val th1 = PROVE_HYP (UNDISCH lemma2) thm in
    let val th2 = remove_defl defl th1 in
      th2
    end end end
  in
    mk_tac1 (intv_one hyp1) (intv_one_val hyp1) goal
  end end end end

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
val t1 = nth 0 (fst newgoal);
val t2 = nth 1 (fst newgoal);
val goal = ([t1,t2],F);

val newgoal = hd (fst(INTV_TAC goal));
val thm = mk_thm (intv_injection_one t2 goal);

*)

fun intf_axiom_test axiom =
  let val term = concl axiom in
  let val (_,eqt) = strip_forall term in
  let val (oper,_) = dest_comb (rhs eqt) in
    oper = intSyntax.int_injection
  end end end
  
fun intf_axiom axiom =
  let val term = concl axiom in
  let val (bvl,eqt) = strip_forall term in
  let val (_,arg) = dest_comb (rhs eqt) in
  let val th1 = ASSUME term in
  let val axiom = integerTheory.INT_POS in
  let val th2 = SPEC arg axiom in
  let val th3 = GENL bvl (SUBS [SYM (SPEC_ALL th1)] th2) in
  let val th4 = (QCONV (intbv_conv THENC normalForms.CNF_CONV))
                (concl th3) 
  in
  let val th5 = EQ_MP th4 th3 in
      th5
  end end end end end end end end end

fun intv_axiom def =
  let val (lht,rht) = dest_eq def in
  let val axiom = integerTheory.INT_POS in
  let val th1 = SPEC (rand rht) axiom in
  let val th2 = SUBS [SYM (ASSUME def)] th1 in
    th2
  end end end end

fun REMOVE_HYP_TAC hypl goal = 
  let fun remove_hyp hypl goal =
    (filter (not o (inv is_member_aconv hypl)) (fst goal), snd goal) 
  in
  let fun remove_hyp_val hypl goal thm = repeat_change ADD_ASSUM hypl thm 
  in
    mk_tac1 (remove_hyp hypl) (remove_hyp_val hypl) goal
  end end 
  
fun NUM_INT_TAC goal =
  (
  fdefdict := [];
  vdefdict := [];
  used := all_var_goal goal;
  let val (goallist0,val0) = (ORIENT_NUM_INEQ_TAC goal) in
  let val (goallist1,val1) = (INTF_TAC (hd goallist0)) in
  let val fnumdict = filter intf_axiom_test (map snd (!fdefdict)) in
  let val thml1 = map intf_axiom fnumdict in
  let val (goallist2,val2) = list_ASSUME_TAC thml1 (hd goallist1) in
  let val hypl = 
    erase_double_aconv (List.concat (map (hyp o snd) (!fdefdict)))
  in
  let val (goallist3,val3) = REMOVE_HYP_TAC hypl (hd goallist2) in
  let val (goallist4,val4) = INTV_TAC (hd goallist3) in
  let val vnumdict = map snd (!vdefdict) in
  let val thml2 = map (intv_axiom) vnumdict in
  let val (goallist5,val5) = list_ASSUME_TAC thml2 (hd goallist4) in
  let val (goallist6,val6) = REMOVE_HYP_TAC vnumdict (hd goallist5) in
    (goallist6, 
     val0 o (mk_list 1) o 
     val1 o (mk_list 1) o 
     val2 o (mk_list 1) o 
     val3 o (mk_list 1) o 
     val4 o (mk_list 1) o 
     val5 o (mk_list 1) o 
     val6)
  end end end end end
  end end end end end end end
  )
  
  
(* test      
show_assums := true;
val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (x:num)``;

val term2 = ``!z:num (y:num). (&z) = ((&(h y:num)):int)``;
val term3 = ``!z . 0 = (0 + (z:num))``;
val goal = ([term3],F);

val (finalgoal,_) = NUM_INT_TAC goal;


val goal2 = hd (fst (INTF_TAC goal));

val hypl = map snd (!fdefdict);
val terml = filter intf_axiom_test hypl;
val thml = map intf_axiom terml;

val goal3 = hd (fst (list_ASSUME_TAC thml goal2));
val goal4 = hd (fst (REMOVE_HYP_TAC hypl goal3));
val goal5 = hd (fst (INTV_TAC  goal4));

val hypl = map snd (!vdefdict);
val thml = map intv_axiom hypl;

val goal6 = hd (fst (list_ASSUME_TAC thml goal5));
val goal7 = hd (fst (REMOVE_HYP_TAC hypl goal6));
*)

(*
val def = ``x20:int = &(x:num)``;

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

val term = hd (fst goal);
 val goal1 = hd (fst (ORIENT_NUM_INEQ_TAC goal));
 val goal2 = hd (fst (INTF_TAC goal1));
 val goal2 = ([hd (fst goal2)],F);
 val goal3 = hd (fst (INTV_TAC goal2));

val hyp1 =  hd (fst goal2);
val finalgoal = intv_one hyp1 goal2;
val thm = mk_thm finalgoal;
intv_one_val hyp1 goal2 thm

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
  case structterm term of
    Numeral => raise UNCHANGED 
  | Integer => raise UNCHANGED
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case structcomb term of
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

(* ADD_FNUM_AXIOMS_TAC *)
local fun is_interesting (var,arity) = 
  let val (_,(imagety,_)) = strip_type_n (type_of var,arity) in
    imagety = ``:num`` andalso arity > 0
  end 
in 
  fun ADD_FNUM_AXIOMS_TAC_w goal =
    let val varal1 = all_vara_goal goal in
    let val varal2 = filter is_interesting varal1 in
    let val axioml = map numf_axiom varal2 in
      list_ASSUME_TAC axioml goal
    end end end
end    
fun ADD_FNUM_AXIOMS_TAC goal = 
  wrap "tactic" "ADD_FNUM_AXIOMS_TAC" "" ADD_FNUM_AXIOMS_TAC_w goal 
(* test
val f = ``f : 'a -> num ``; 
val arity = 1; 
  normalForms.CNF_CONV (concl it);
*)


end