structure blibConv (* :> blibConv *) =
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

(* BOOL CONV *)
local fun is_interesting_in term subterm =  
  free_in subterm term andalso
  has_boolty subterm andalso
  not (subterm = T) andalso
  not (subterm = F) 
in
fun find_free_bool_aux term subterm =
  case structterm subterm of
    Numeral => []
  | Integer => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case structcomb subterm of
      Conj => find_free_bool_binop term subterm
    | Disj => find_free_bool_binop term subterm
    | Neg => find_free_bool_unop term subterm
    | Imp_only => find_free_bool_binop term subterm
    | Forall => find_free_bool_quant term subterm
    | Exists => find_free_bool_quant term subterm   
    | _ =>   
      let val (operator,argl) = strip_comb subterm in
        filter (is_interesting_in term) argl @
        find_free_bool_list term (operator :: argl)
      end

    )             
  | Abs => raise CONV_ERR "find_free_bool_aux" "abstraction"
and find_free_bool_list term subterml =
  merge_aconv (map (find_free_bool_aux term) subterml)
and find_free_bool_quant term subterm =
  let val (bvl,t) = strip_quant subterm in
    find_free_bool_aux term t
  end  
and find_free_bool_binop term subterm =
  find_free_bool_list term [lhand subterm,rand subterm] 
and find_free_bool_unop term subterm =
  find_free_bool_aux term (rand subterm)
end  
 
fun find_free_bool term = erase_double_aconv (find_free_bool_aux term term) 

(* term should have type bool *)
fun bool_conv_sub_w subterm term =
  (* preparation *)  
  let val disj1 = SPEC subterm BOOL_CASES_AX in
  let val eqth1 = ASSUME (lhand (concl disj1)) in
  let val eqth2 = ASSUME (rand (concl disj1)) in
  (* first part  *)
  (* lemma *)
  let val lemma1 = ASSUME subterm in
  let val lemma2 = EQT_INTRO lemma1 in
  let val lemma3 = ASSUME (mk_neg subterm) in
  let val lemma4 = EQF_INTRO lemma3 in
  let val th11 = ASSUME term in
  (* true part *)
  let val th12T = SUBS [eqth1] th11 in
  let val th13T = PROVE_HYP lemma2 th12T in
  let val th14T = DISCH subterm th13T in
  (* false part *)
  let val th12F = SUBS [eqth2] th11 in
  let val th13F = PROVE_HYP lemma4 th12F in
  let val th14F = DISCH (mk_neg subterm) th13F in
  (* and *)
  let val th15 = CONJ th14T th14F in
  let val th16 = DISCH term th15 in
  
  (* second part *)
  (* lemma *)
  let val lemma21 = ASSUME (concl lemma2) in
  let val lemma22 = EQT_ELIM lemma21 in
  let val lemma23 = ASSUME (concl lemma4) in
  let val lemma24 = EQF_ELIM lemma23 in
  (* true part *)
  let val goal1 = ([lhand(concl disj1), concl th15],hd (hyp th15)) in
  let val (_,fnT) = SUBST_TAC [eqth1] goal1 in  
  let val th21T = ASSUME (lhand (concl th15)) in
  let val th22T = ASSUME subterm in
  let val th23T = MP th21T th22T in
  let val th24T = fnT [th23T] in
  let val th25T = PROVE_HYP lemma22 th24T in
  (* false part *)
  let val goal2 = ([rand(concl disj1), concl th15],hd (hyp th15)) in
  let val (_,fnF) = SUBST_TAC [eqth2] goal1 in  
  let val th21F = ASSUME (rand (concl th15)) in
  let val th22F = ASSUME (mk_neg subterm) in
  let val th23F = MP th21F th22F in
  let val th24F = fnF [th23F] in
  let val th25F = PROVE_HYP lemma24 th24F in 
  (* disj cases *)
  let val lemma25 = CONJUNCT1 (ASSUME (concl th15)) in
  let val lemma26 = CONJUNCT2 (ASSUME (concl th15)) in
  let val th26 = DISJ_CASES disj1 th25T th25F in
  let val th27 = LIST_PROVE_HYP [lemma25,lemma26] th26 in
  let val th28 = DISCH (concl th15) th27 in
  (* together *)
    IMP_ANTISYM_RULE th16 th28
  end end end end end 
  end end end end end 
  end end end end end
  end end end end end 
  end end end end end 
  end end end end end
  end end end end end 
  end end end end
fun bool_conv_sub subterm term = 
  wrap "conv" "bool_conv_sub" 
    ((term_to_string term) ^ " : " ^ (term_to_string subterm))
    (bool_conv_sub_w subterm) term
(* test
val subterm = ``!f:num -> bool . f x``;
val term = ``P (!f:num -> bool . f x) (!f:num -> bool . f x): bool``;
bool_conv_sub subterm term;

val term = ``P (x = x + 1) ==> P F ``;
val subterm = ``x = x + 1``;
*)
fun bool_conv_sub_one term =
  let val l = find_free_bool term in
    case l of
      [] => raise UNCHANGED
    | b :: m => bool_conv_sub b term
  end

fun bool_conv_sub_all term = 
  wrap "conv" "bool_conv_sub_all" "" (REPEATC bool_conv_sub_one) term

fun bool_conv_aux term = 
  case structterm term of
    Numeral => raise UNCHANGED 
  | Integer => raise UNCHANGED
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case structcomb term of
      Forall => ((STRIP_QUANT_CONV bool_conv_sub_all) THENC 
                 (STRIP_QUANT_CONV bool_conv_aux)) 
                   term
    | Exists => ((STRIP_QUANT_CONV bool_conv_sub_all) THENC 
                 (STRIP_QUANT_CONV bool_conv_aux)) 
                   term     
    | _ => COMB_CONV bool_conv_aux term
    )
  | Abs => raise CONV_ERR "bool_conv_aux" "abstraction"

fun bool_conv term =
  wrap "conv" "bool_conv" "" (bool_conv_sub_all THENC bool_conv_aux) term

(* test
val term = ``!x. g (!z. z = 0) /\ g (!z. x = z)``;
val term = ``!x. x + 1 = 0``;
val subterml = find_free_bool term;
val subterml2 = find_bound_bool term;
bool_conv_quant term;
val subterm = ``!x.x``;
val term = ``P (!x.x) (!y.y): bool ``;
bool_conv term; 
find_free_bool term;
bool_conv_sub subterm term;
*)

(* FUN_CONV *)
(* find *)
fun find_free_abs_aux term subterm =
  case structterm subterm of
    Numeral => []
  | Integer => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case structcomb subterm of
      Forall => let val (bvl,t) = strip_forall subterm in
                  find_free_abs_aux term t
                end  
    | Exists => let val (bvl,t) = strip_exists subterm in
                  find_free_abs_aux term t
                end      
    | _ => let val (operator,arg) = dest_comb subterm in
             (find_free_abs_aux term operator) @ (find_free_abs_aux term arg)
           end  
    )
  | Abs => let val (bvl,t) = strip_abs subterm in
             if free_in subterm term
             then subterm :: find_free_abs_aux term t
             else find_free_abs_aux term t  
           end
           
fun find_free_abs term = erase_double_aconv (find_free_abs_aux term term)

fun fun_axiom_w abs =
  let val (bvl,t) = strip_abs abs in
  let val th1 = REFL abs in
  let val th2 = list_AP_THM th1 bvl in
  let val th3 = RAND_CONV (REDEPTH_CONV BETA_CONV) (concl th2) in
  let val th4 = EQ_MP th3 th2 in
    th4
  end end end end end
fun fun_axiom abs = wrap "conv" "fun_axiom" "" fun_axiom_w abs 

fun eq_conj_subs thm =
  let val th0 = CONJUNCT1 thm in
  let val th1 = CONJUNCT2 thm in
  let val th2 = SUBS [th0] th1 in
    th2
  end end end

fun and_strip_bvl_forall_mp bvl term = 
  let val th0 = ASSUME term in
  let val th1 = CONJUNCT1 th0 in
  let val th2 = CONJUNCT2 th0 in
  let val newbvl = mk_newvarl bvl (all_var_thm th0) in
  let val th3 = SPECL newbvl th1 in 
  let val th4 = SPECL newbvl th2 in
  let val th5 = CONJ th3 th4 in
  let val th6 = GENL newbvl th5 in
    DISCH term th6
  end end end end end 
  end end end

(* test   
val newbvl = bvl;
val (bvl,t) = strip_abs abs;
show_assums:= true;
*)

fun fun_conv_sub_w abs term =
  (* term *)
  let val ty = type_of abs in
  let val newname = mk_newname "f" (map namev_of (all_var term)) in
  let val v = (mk_var (newname,ty)) in (* fresh var *)
  let val (bvl,t) = strip_abs abs in
  (* axiom *)
  let val axiom1 = fun_axiom abs in
  let val axiom2 = GENL bvl axiom1 in
  (* first part *)
  let val th11 = ASSUME term in
  let val th12 = CONJ axiom2 th11 in 
  let val t1 = mk_conj (concl axiom2,term) in
  let val t2 = subst [abs |-> v] t1 in (* substitution *)
  let val t3 = mk_exists (v,t2) in
  let val th13 = EXISTS (t3,abs) th12 in
  let val th14 = DISCH term th13 in
  (* second part *) 
  let val th21 = ASSUME (concl th13) in 
  let val th22 = CONJ axiom2 th21 in
    (* put the existential outside *)
  let val t10 = mk_conj (concl axiom2,concl th13) in
  let val eqth10 = RIGHT_AND_EXISTS_CONV t10 in
  let val th23 = EQ_MP eqth10 th22 in
    (* remove the existential and deduce something *)
  let val (bv,t4) = dest_exists (concl th23) in
  let val th31 = ASSUME t4 in
  let val th32 = CONJUNCT1 th31 in
  let val th33 = CONJUNCT1 (CONJUNCT2 th31) in
  let val th34 = CONJUNCT2 (CONJUNCT2 th31) in
  let val th35 = CONJUNCT2 th31 in
  
  let val th36 = CONJ th32 th33 in
  let val th37 = and_strip_bvl_forall_mp bvl (concl th36) in
  let val th38 = MP th37 th36 in
  
  let val newbvl = mk_newvarl bvl (all_var_thm th38) in
  let val th39 = SPECL newbvl th38 in 
  let val th40 = CONJUNCT1 th39 in
  let val th41 = SYM (CONJUNCT2 th39) in
  let val th42 = TRANS th40 th41 in
  let val th43 = GENL newbvl th42 in
  let val th44 = EXTL bvl th43 in 
  let val th45 = SYM th44 in
  let val th46 = SUBS [th45] th35 in (* substitution *)
  let val th47 = DISCH t4 th46 in
    (* end *)
  let val th48 = GEN v th47 in
  let val th49 = FORALL_IMP_CONV (concl th48) in 
  let val th50 = EQ_MP th49 th48 in
  let val th51 = LAND_CONV EXISTS_AND_CONV (concl th50) in
  let val th52 = EQ_MP th51 th50 in
 
  let val th53 = CONJ axiom2 th21 in
  let val th54 = MP th52 th53 in
  let val th55 = CONJUNCT2 th54 in
  let val th56 = DISCH (concl th13) th55 in
    (* together *)
    IMP_ANTISYM_RULE th14 th56
  end end end end end 
  end end end end end 
  end end end end end 
  end end end end end 
  
  end end end end end 
  end end end end end 
  end end end end end 
  end end end end end 
  end end end end end end 
fun fun_conv_sub abs term =
  wrap "conv" "fun_conv_sub" 
   ("abs: " ^ (term_to_string abs) ^ "term: " ^ (term_to_string term))
   (fun_conv_sub_w abs) term
   
(* test
val term = ``P (\x y. x + y + z) : bool``;
val abs = ``\x y. x + y + z``;
fun_conv_sub abs term;
fun_axiom term;
*)
fun fun_conv_sub_one term =
  let val l = find_free_abs term in
    case l of
      [] => raise UNCHANGED
    | abs :: m => fun_conv_sub abs term
  end
  
fun fun_conv_sub_all term = REPEATC fun_conv_sub_one term
(* test 
show_assums :=  true;
val abs = ``\x y . x + y``;
val term = ``(P (\x y. x + y) (\y.y)):bool``;
fun_conv_sub abs term;
*)

(* test 
show_assums :=  true;
val term = ``!z. (P (\x. x + z)):bool``;
fun_conv_quant_aux term;
*)

(* term of type bool *)
fun fun_conv_aux term = 
  case structterm term of
    Numeral => raise UNCHANGED 
  | Integer => raise UNCHANGED
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case structcomb term of
      Forall => ((STRIP_QUANT_CONV fun_conv_sub_all) THENC
                 (STRIP_QUANT_CONV fun_conv_aux)) 
                   term
    | Exists => ((STRIP_QUANT_CONV fun_conv_sub_all) THENC
                 (STRIP_QUANT_CONV fun_conv_aux)) 
                   term       
    | _ => COMB_CONV fun_conv_aux term
    )
  | Abs => raise UNCHANGED

fun fun_conv term = 
  wrap "conv" "fun_conv" "" (fun_conv_sub_all THENC fun_conv_aux) term


(* test 
val term = ``P (\x. x + 1) (\y.y) /\ !x. Q (\z. z + x)``;
val term = ``P (\x z. x + z):bool``;
val term = ``P (\x. (x = \z.z) ):bool`` ;
fun_conv term;
find_free_abs term ;
*)

(* APP CONV *)   
fun app_axiom_w appname term =
  let val (oper,arg) = dest_comb term in  
  let val opty = type_of oper in
  (* app *)
  let val appty = mk_type ("fun",[opty,opty]) in  
  let val app = mk_var (appname,appty) in
  (* operator *)
  let val newoper = mk_var ("f",opty) in
  (* arg *)
  let val newarg = mk_var ("x",type_of arg) in
  (* term *)
  let val t1 = list_mk_abs ([newoper,newarg],mk_comb (newoper,newarg)) in
  let val t2 = mk_eq (app,t1) in
  (* axiom *)
  let val th1 = ASSUME t2 in
  let val th2 = CONV_RULE (list_FUN_EQ_CONV [newoper,newarg]) th1 in
  let val th3 = CONV_RULE (REDEPTH_CONV BETA_CONV) th2 in
    th3
  end end end end end
  end end end end end
  end
fun app_axiom appname term =
  wrap "conv" "app_axiom" "" (app_axiom_w appname) term 
  

(* test
show_assums :=  true;
val term = ``f a b c``;
val arity = 3;
val lowarity = 1;
val appname = "App";
*)

fun app_conv_basic appname term =
  let val (oper,arg) = dest_comb term in  
  let val th1 = app_axiom appname term in
  let val th2 = SYM (SPECL [oper,arg] th1) in
    th2
  end end end

fun app_conv_sub appname lowarity arity term =
   if lowarity = arity then raise UNCHANGED
   else if lowarity < arity
      then (
           RATOR_CONV (app_conv_sub appname lowarity (arity -1))
           THENC app_conv_basic appname 
           )
           term
   else raise CONV_ERR "app_conv_sub" "lowarity > arity"
   


fun app_conv appname fvclal bvl term = 
  case structterm term of
    Comb =>
    (
    case structarity term of  
      Binop => BINOP_CONV (app_conv appname fvclal bvl) term 
    | Unop => RAND_CONV (app_conv appname fvclal bvl) term 
    | Quant => let val (qbvl,_) = strip_quant term in
                 STRIP_QUANT_CONV (app_conv appname fvclal (qbvl @ bvl)) term
               end
    | _ =>
       let val (oper,_) = strip_comb term in
       let val arity = get_arity term in
       let val lowarity = if is_member oper bvl then 0 else lookup oper fvclal
       in
        (ARG_CONV (app_conv appname fvclal bvl) THENC 
        app_conv_sub appname lowarity arity) 
        term 
       end end end
     )
  | _ => raise UNCHANGED 


local fun change_arity tyl (fvc,a)  =
  if is_member (type_of fvc) tyl then (fvc,0) else (fvc,a)
in
fun APP_CONV appname goal term =
  let val fvclal1 = collapse_lowestarity (merge (map get_fvcal (fst goal))) in
  let val tyl = map type_of (get_bvl_goal goal) in
  let val fvclal2 = map (change_arity tyl) fvclal1 in
    app_conv appname fvclal2 [] term
  end end end   
end

      
(* test
show_assums :=  true;
val subterm = ``f a b ``;
val appname = "App";
val term = ``(f a b = 2) /\ (f = g)``;
val goal = ([term],F);
*)
 
fun ADD_HIGHER_ORDER_TAC_w goal =
  let val appname = mk_newname "App" (map namev_of (all_var_goal goal)) in
  let fun add_higher_order goal = 
    conv_hyp (QCONV (APP_CONV appname goal)) goal
  in  
  let fun add_higher_order_val goal thm =
    let val eqthl = map (QCONV (APP_CONV appname goal)) (fst goal) in
    let val defl = merge_aconv (map hyp eqthl) in
    let val lemmal = map (UNDISCH o fst o EQ_IMP_RULE) eqthl in
    let val th0 = LIST_PROVE_HYP lemmal thm in
    let val th1 = remove_defl defl th0 in
      th1
    end end end end end
  in
    if firstorder_goal goal 
    then ALL_TAC goal
    else mk_tac1 add_higher_order add_higher_order_val goal
  end end end

fun ADD_HIGHER_ORDER_TAC goal = 
  wrap "tactic" "ADD_HIGHER_ORDER_TAC" "" ADD_HIGHER_ORDER_TAC_w goal 
 

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

end
