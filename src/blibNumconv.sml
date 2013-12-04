structure blibNumconv (*:> blibNumconv*) =
struct

open HolKernel Abbrev boolLib 
     blibBtools blibDatatype 
     blibSyntax blibBrule blibBconv blibBtactic
     blibExtractvar blibExtracttype blibFreshvar


fun NUMCONV_ERR function message =
  HOL_ERR{origin_structure = "blibNumconv",
          origin_function = function,
          message = message}

(* NUMERAL TO INTEGER TRANSLATION *)
(* global reference *)
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
  
  
fun mk_listn_aux nb str start =
  if nb = 0 then []
  else if nb < 0 then raise NUMCONV_ERR "mk_listn_aux" "negative number" 
  else (str ^ (Int.toString start)) :: mk_listn_aux (nb - 1) str (start + 1)
  
fun mk_listn nb str = mk_listn_aux nb str 1
  
(* INTF_TAC *)  
fun inj_fun_axiom (op1,a) =
  let val (argtyal,imtya) = strip_type_n (type_of op1,a) in 
  let val argtyl = map fst argtyal in
  let val namel = mk_listn a "x" in  
  let val opty2 = mk_funtype (map type_num_to_int argtyl,
                              type_num_to_int (fst imtya)) in
  let val op2 = mk_newvar (mk_var (namev_of op1, opty2)) (!used) in
  let val argln = mk_newvarl (mk_varl (namel,argtyl)) (op2 :: !used) in
  let val argli = mk_newvarl (mk_varl (namel,map type_num_to_int argtyl)) 
                    (op2 :: (!used)) 
  in
  let val injectl = map inject_num argln in
  let val coercl = map coerc_int (mk_couplel argln argli) in
  (* def *)
  let val t1 = list_mk_comb (op1,coercl) in
  let val t2 = if fst imtya = ``:num``
               then mk_comb (intSyntax.int_injection,t1) 
               else t1
  in
  let val t3 = list_mk_abs (argli,t2) in


  let val t4 = mk_eq (op2,t3) in
      (* axiom *)
  let val th1 = ASSUME t4 in 
  let val th2 = CONV_RULE (list_FUN_EQ_CONV argli) th1 in
  let val th3 = SPECL injectl th2 in
  let val th4 = CONV_RULE (REDEPTH_CONV BETA_CONV) th3 in
  let val th5 = SPEC_ALL integerTheory.NUM_OF_INT in
  let val th6 = CONV_RULE (REWRITE_CONV [th5]) th4 in
  let val th7 = GENL argln th6 in 
        (
        used := op2 :: (!used);
        th7
        )
  end end end end end 
  end end end end end 
  end end end end end 
  end end end end end 


local fun test (var,a) = (a > 0) andalso not (var = intSyntax.int_injection)
in
fun get_fal term = filter test (get_fvcal term)
end

fun get_fal_list terml = merge (map get_fal terml)
fun get_fal_goal (terml,concl) = get_fal_list (concl :: terml)

fun is_numty ty = ty = ``:num``

fun test_intf_tac (f,arity) = 
  let val (argtyl,imty) = strip_type_n (type_of f,arity) in
     exists is_numty ((fst imty) :: (map fst argtyl))
  end

fun INTF_TAC goal =
  let val fal = filter test_intf_tac (get_fal_goal goal) in
  let val funaxioml = map inj_fun_axiom fal in
  let val funrthml = map (SYM o SPEC_ALL) funaxioml in
  let val oprthml = [
  SYM (SPEC_ALL integerTheory.INT_INJ),
  SYM (SPEC_ALL integerTheory.INT_ADD),
  SPEC_ALL int_arithTheory.INT_NUM_SUB,
  SYM (SPEC_ALL integerTheory.INT_MUL),
  SYM (SPEC_ALL integerTheory.INT_LE),
  SYM (SPEC_ALL integerTheory.INT_LT)
  ]
  in
  let val eqthl = map (QCONV (REWRITE_CONV (funrthml @ oprthml))) (fst goal) in 
  let val defl = merge_aconv (map hyp eqthl) in
  let val randl = map (rand o concl) eqthl in
  let val finalgoal = (erase_double_aconv (defl @ randl),F) in
  let fun intf goal = finalgoal in
  let fun intf_val goal thm =
    let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in 
    let val th1 = list_PROVE_HYP lemmal thm in
    let val th2 = remove_defl defl th1 in
      th2
    end end end
  in
    (mk_tac1 intf intf_val goal,funaxioml)
  end end
  end end end end end
  end end end
 
(* BOUND VARIABLES *)
fun mk_subt_abs (bv,subterm,term) =
   let val s = [subterm |-> bv] in
   let val t = subst s term in
     mk_abs (bv,t)
   end end   
     
fun intbv_conv_FST term =   
  let val (bv,t) = dest_forall term in
    if type_of bv = ``:num``
    then
      let val th1 = int_arithTheory.INT_NUM_FORALL in
      let val eqth2 = ((RAND_CONV (RENAME_VARS_CONV [namev_of bv])) 
                      THENC (LAND_CONV (RENAME_VARS_CONV [namev_of bv])))
                      (concl th1) 
      in
      let val th3 = EQ_MP eqth2 th1 in
      let val intbv = mk_var (namev_of bv,``:int``) in
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

fun INTBV_TAC goal = CONV_HYP_TAC (intbv_conv THENC normalForms.CNF_CONV) goal

(* functions axioms *)
fun intf_axiom_test faxiom =
  let val term = concl faxiom in
  let val (_,eqt) = strip_forall term in
    intSyntax.is_injected (rhs eqt) (* to be verified *)
  end end
  
(* to be verified *)
fun intf_axiom faxiom =
  let val term = concl faxiom in
  let val (bvl,eqt) = strip_forall term in
  let val (_,arg) = dest_comb (rhs eqt) in
  let val axiom1 = integerTheory.INT_POS in
  let val th1 = SPEC arg axiom1 in
  let val th2 = GENL bvl (SUBS [SYM (SPEC_ALL faxiom)] th1) in
  let val th3 = (QCONV (intbv_conv THENC normalForms.CNF_CONV))
                (concl th2) 
  in
  let val th4 = EQ_MP th3 th2 in
      th4
  end end end end 
  end end end end

(* test 
val term = concl (hd thml1);

*)




(* FREE VARIABLES *)
fun intfv_def term = 
  let val v1 = mk_var (namev_of (rand term),``:int``) in 
  let val v2 = mk_newvar v1 (!used) in
    (
    used := v2 :: (!used);
    mk_eq (v1,term)
    )
  end end
 
local fun test term t = 
  if not (free_in t term) then false 
  else if not (structterm t = Comb) then false
  else if not (rator t = intSyntax.int_injection) then false
  else if not (is_var (rand t) orelse is_const (rand t)) then false
  else if numSyntax.is_numeral (rand t) then false
  else true 
in 
local fun get term = find_terms (test term) term
in
fun INTFV_TAC goal = 
  let val terml1 = (fst goal) in  
  let val terml2 = merge_aconv (map get terml1) in
  let val defl = map intfv_def terml2 in
  let val thml = map (SYM o ASSUME) (defl) in
  let val eqthl =  map (QCONV (REWRITE_CONV thml)) terml1 in
  let fun intfv goal = (defl @ map (rhs o concl) eqthl,F) in
  let fun intfv_val goal thm =
    let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
    let val th1 = list_PROVE_HYP lemmal thm in
    let val th2 = remove_defl defl th1 in
      th2
    end end end
  in
  ((mk_tac1 intfv intfv_val) goal, defl)
  end end end end end
  end end
end
end

(* free variables axioms *)
fun intfv_axiom def =
  let val (lht,rht) = dest_eq def in
  let val axiom = integerTheory.INT_POS in
  let val th1 = SPEC (rand rht) axiom in
  let val th2 = SUBS [SYM (ASSUME def)] th1 in
    th2
  end end end end

fun ADD_CONDINT_TAC goal =
  let val cl = get_cl_goal goal in
  let val condint = Term.inst [``:'a`` |-> ``:int``] boolSyntax.conditional in
  let val axiom = INST_TYPE [``:'a`` |-> ``:int``] COND_CLAUSES in
    if is_member condint cl 
    then ASSUME_TAC axiom goal
    else ALL_TAC goal
  end end end
                          
(* MAIN FUNCTION *)
fun NUM_INT_TAC_v goal =
  (
  used := all_var_goal goal;
  let val (goall0,val0) = (ORIENT_NUM_INEQ_TAC goal) in
  let val ((goall1,val1),thml1) = (INTF_TAC (hd goall0)) in
  let val thml2 = map intf_axiom (filter intf_axiom_test thml1) in
  let val (goall2,val2) = list_ASSUME_TAC thml2 (hd goall1) in
  let val fdefl = merge_aconv (map hyp thml1) in
  let val (goall3,val3) = REMOVE_HYPL_TAC fdefl (hd goall2) in
  let val ((goall4,val4),vdefl) = INTFV_TAC (hd goall3) in
  let val thml3 = map (intfv_axiom) vdefl in
  let val (goall5,val5) = list_ASSUME_TAC thml3 (hd goall4) in
  let val (goall6,val6) = REMOVE_HYPL_TAC vdefl (hd goall5) in
  let val (goall7,val7) = INTBV_TAC (hd goall6) in
  let val (goall8,val8) = ADD_CONDINT_TAC (hd goall7) in
  let val (finalgoall,validation) = 
     (goall7, 
     val0 o (mk_list 1) o 
     val1 o (mk_list 1) o 
     val2 o (mk_list 1) o 
     val3 o (mk_list 1) o 
     val4 o (mk_list 1) o 
     val5 o (mk_list 1) o 
     val6 o (mk_list 1) o 
     val7 o (mk_list 1) o 
     val8)
  in
    (finalgoall,validation)
  end end end end end
  end end end end end 
  end end end
  )
  
fun NUM_INT_TAC goal = VALID NUM_INT_TAC_v goal  
  
(* test      
show_assums := true;

val term = ``!z. f (z:int) (x:num) = (0:num)``; 
val goal = ([term],F);

val term1 = ``!z:num (y:num). f z (g y:bool) = (0:num) + (x:num)``;
val term2 = ``!z:num (y:num). (&z) = ((&(h y:num)):int)``;
val term3 = ``!z . 0 = (0 + (z:num))``;
val term = `` App x y = (5:int)``; (* shouldn't change *)

val term1 = `` (& (y:num):int) = f (0:int) ``;
val term2 = `` (& (y:num):int) = 0:int ``;
val goal = ([term1,term2],F);
val term = ``∀y. (&(y:num):int) + (&(z:num):int) = 0``;
val goal = ([term],F);

(* error1 variable name problem *)
val term1 = `` App x y = (5:num)``;
val term2 = `` App (x:int) (y:num) : bool ``;
val goal = ([term1,term2],F);

val term1 = `` App x y = (5:num)``;
val term2 = `` App1 (x:int) (y:num) : bool ``;
val goal = ([term1,term2],F);

*)

end