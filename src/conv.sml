structure conv :> conv =
struct

(*
load "listtools"; open listtools;
load "tools"; open tools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
*)

(*
Beta 
Eta
Cnf  - to eliminate if then else and ?! mostly 
       should try to write my own conv for that to prevent it from 
       eliminating => because people won't recognize the output
              
Bool - no boolean argument except variables
Fun  - no lambda abstraction 
App  - no second order
Num  - add num axiom (suppose there is no abstraction left)
Predicate -

Use different variables name to prevent cnf_conv from renaming them
At least , memorise them into list so that they can be printed differently
*)

open HolKernel Abbrev boolLib normalForms (* numSyntax *) (* arithmeticTheory *)
     stringtools listtools tools mydatatype 
     extractvar extracttype 

fun CONV_ERR function message =
    HOL_ERR{origin_structure = "conv",
	    origin_function = function,
            message = message}


(* BETA CONV *)
fun beta_conv term = (REDEPTH_CONV BETA_CONV) term;
(* ETA CONV *)
fun eta_conv term = (REDEPTH_CONV ETA_CONV) term;

(* CNF CONV *)
  (* eliminate unused quantifier normalForms.CNF_CONV ``?x. !x. p x``; *)
  (* =>, ?! and if then else *)
fun cnf_conv term = normalForms.CNF_CONV term

(* BOOL CONV *)
local fun is_interesting_in term subterm =  
  free_in subterm term andalso
  has_boolty subterm andalso
  is_logical subterm 
in
fun find_free_bool_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connector subterm of
      Forall => find_free_bool_quant term subterm
    | Exists => find_free_bool_quant term subterm   
    | Conj => find_free_bool_binop term subterm
    | Neg => find_free_bool_unop term subterm
    | Imp_only => find_free_bool_binop term subterm
    | Disj => find_free_bool_binop term subterm
    | App =>   
      let val (operator,argl) = strip_comb subterm in
        filter (is_interesting_in term) argl @
        find_free_bool_list term (operator :: argl)
      end

    )             
  | Abs => let val (bvl,t) = strip_abs subterm in
             find_free_bool_aux term t
           end 
and find_free_bool_list term subterml =
  List.concat (map (find_free_bool_aux term) subterml)
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
(* bound *)     
local fun is_interesting_in term subterm =  
  bound_by_quant subterm term andalso
  has_boolty subterm andalso
  is_logical subterm 
in
fun find_bound_bool_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connector subterm of
      Forall => find_bound_bool_quant term subterm
    | Exists => find_bound_bool_quant term subterm   
    | Conj => find_bound_bool_binop term subterm
    | Neg => find_bound_bool_unop term subterm
    | Imp_only => find_bound_bool_binop term subterm
    | Disj => find_bound_bool_binop term subterm
    | App => 
      let val (operator,argl) = strip_comb subterm in
        filter (is_interesting_in term) argl @
        find_bound_bool_list term (operator :: argl)
      end
    )             
  | Abs => let val (bvl,t) = strip_abs subterm in
             find_bound_bool_aux term t
           end 
and find_bound_bool_list term subterml =
  List.concat (map (find_bound_bool_aux term) subterml)
and find_bound_bool_quant term subterm =
  let val (bvl,t) = strip_quant subterm in
    find_bound_bool_aux term t
  end  
and find_bound_bool_binop term subterm =
  find_bound_bool_list term [lhand subterm,rand subterm] 
and find_bound_bool_unop term subterm =
  find_bound_bool_aux term (rand subterm)
end  
   
fun find_bound_bool term = erase_double_aconv (find_bound_bool_aux term term)

(* term should have type bool *)
fun bool_conv_sub subterm term =
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
  let val th26 = DISJ_CASES disj1 th25T th25F in
  let val th27 = list_conj_hyp th26 in
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
  end end

(* test
val subterm = ``!f:num -> bool . f x``;
val term = ``P (!f:num -> bool . f x) (!f:num -> bool . f x): bool``;
bool_conv_sub subterm term;
*)
fun bool_conv_subl subterml term = 
  case subterml of
    [] => raise UNCHANGED
  | subterm :: m => ((bool_conv_sub subterm) THENC (bool_conv_subl m)) term
  
fun bool_conv_quant term =
  let val terml = find_bound_bool term in
    STRIP_QUANT_CONV (bool_conv_subl terml) term 
  end 

fun bool_conv_aux term = 
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connector term of
      Forall => ((STRIP_QUANT_CONV bool_conv_aux) THENC bool_conv_quant) term
    | Exists => ((STRIP_QUANT_CONV bool_conv_aux) THENC bool_conv_quant) term        
    | _ => COMB_CONV bool_conv_aux term
    )
  | Abs => raise UNCHANGED

fun bool_conv term =
  let val terml = find_free_bool term in
    (bool_conv_aux THENC (bool_conv_subl terml)) term
  end

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


(* PRINTING IDEA *)
(* 
 = :bool -->  <=> 
 = :bool -->   =  
depend on the arguments 
*)
(*
true --> $true
true --> btrue 
*)

(* NUM CONV *)
(* find *)
local fun is_interesting_in term subterm = 
  has_numty subterm andalso 
  free_in subterm term andalso 
  not (numSyntax.is_numeral subterm)
in
fun find_free_num term = 
  erase_double_aconv (filter (is_interesting_in term) (all_subterm term))
end 
  
(* term should start with a quantifier *)  
local fun is_interesting_in term subterm = 
  bound_by_quant subterm term andalso
  has_numty subterm andalso 
  not (numSyntax.is_numeral subterm)
in 
fun find_bound_num term =  
  erase_double_aconv (filter (is_interesting_in term) (all_subterm term))
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
  let val terml1 = filter is_var terml in
  let val terml2 = filter is_not_var terml in
    STRIP_QUANT_CONV 
      ((num_conv_conj terml2) THENC (num_conv_imp terml1))
      term  
  end end end

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
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connector term of
      Forall => ((STRIP_QUANT_CONV num_conv_aux) THENC num_conv_forall) term
    | Exists => ((STRIP_QUANT_CONV num_conv_aux) THENC num_conv_exists) term        
    | _ => COMB_CONV num_conv_aux term
    )
  | Abs => raise CONV_ERR "num_conv" "abstraction"

fun num_conv term =
  let val terml = find_free_num term in
    (num_conv_aux THENC (num_conv_conj terml)) term
  end
  
(* test
val term = ``(a = 0) /\ ?x y. (x = 0) /\ (!x. x + 1 = z) /\ (f y = 0)``;
*)

(* FUN CONV *)  
(* find *)
fun find_free_abs_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connector subterm of
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

fun find_bound_abs_aux term subterm = (* term should start with a quantifier *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connector subterm of
      Forall => let val (bvl,t) = strip_forall subterm in
                  find_bound_abs_aux term t
                end  
    | Exists => let val (bvl,t) = strip_exists subterm in
                  find_bound_abs_aux term t
                end      
    | _ => let val (operator,arg) = dest_comb subterm in
             (find_bound_abs_aux term operator) @ (find_bound_abs_aux term arg)
           end  
    )
  | Abs => let val (bvl,t) = strip_abs subterm in
             if bound_by_quant subterm term
             then subterm :: find_bound_abs_aux term t
             else find_bound_abs_aux term t  
           end

fun find_bound_abs term = erase_double_aconv (find_bound_abs_aux term term)
  

(* input is ``f = \x y. x + y`` *)
fun fun_axiom term =
  let val funv = lhs term in
  let val abst = rhs term in
  let val (bvl,t) = strip_abs abst in
  (* useful axiom *)
  let val axiom1 = list_fun_eq_conv bvl term in
  let val axiom2 = REFL abst in
  let val axiom3 = list_ap_thm axiom2 bvl in
  let val axiom4 = LAND_CONV LIST_BETA_CONV (concl axiom3) in
  let val axiom5 = EQ_MP axiom4 axiom3 in
  let val axiom6 = SYM axiom1 in
  (* first part *)
  let val th11 = ASSUME term in
  let val th12 = EQ_MP axiom1 th11 in 
  let val th13 = STRIP_QUANT_CONV (RAND_CONV LIST_BETA_CONV) (concl th12) in
  let val th14 = EQ_MP th13 th12 in 
  let val th15 = DISCH term th14 in
  (* second part *)
  let val th21 = ASSUME (concl th14) in
  let val th22 = SPECL bvl th21 in
  let val th23 = TRANS th22 axiom5 in
  let val th24 = GENL bvl th23 in  
  let val th25 = EQ_MP axiom6 th24 in
  let val th26 = DISCH (concl th14) th25 in
  (* together *)
    IMP_ANTISYM_RULE th15 th26
  end end end end end
  end end end end end
  end end end end end
  end end end end end
  handle _ => raise CONV_ERR "fun_axiom" (term_to_string term)

(* test 
show_assums := true;
val term = ``f = \x y. x + y``;
fun_axiom term;
*)

(* term should have type bool *)
fun fun_conv_sub abs term =
  (* term *)
  let val ty = type_of abs in
  let val v = create_newvar (mk_var ("f",ty)) (all_var term) in 
  let val t1 = mk_eq (v,abs) in   
  let val (bvl,t2) = strip_abs abs in
  (* axiom *)
  let val axiom1 = fun_axiom t1 in
  let val (axiom2,axiom3) = EQ_IMP_RULE axiom1 in
  let val axiom4 = REFL t2 in
  let val axiom5 = GENL bvl axiom4 in
  let val lemma1 = UNDISCH axiom2 in
  let val lemma2 = UNDISCH axiom3 in
  (* first part *)
  let val th11 = ASSUME term in
  let val th12 = SYM (ASSUME t1) in  
  let val th13 = SUBS [th12] th11 in  (* to be checked *)
  let val th14 = PROVE_HYP lemma2 th13 in
  let val th15 = DISCH (concl lemma1) th14 in
  let val th16 = GEN v th15 in
  let val th17 = DISCH term th16 in
  (* second part *) 
  let val th21 = ASSUME (concl th16) in
  let val th22 = SPEC abs th21  in (* to be checked *)
  let val th23 = LAND_CONV (STRIP_QUANT_CONV (LAND_CONV LIST_BETA_CONV)) 
                   (concl th22) in    
  let val th24 = EQ_MP th23 th22 in
  let val th25 = MP th24 axiom5 in
  let val th26 = DISCH (concl th16) th25 in 
    (* together *)
    IMP_ANTISYM_RULE th17 th26
  end end end end end 
  end end end end end 
  end end end end end 
  end end end end end 
  end end end
  handle _ => raise CONV_ERR "fun_conv_sub" 
              ("abs: " ^ (term_to_string abs) ^
              "term: " ^ (term_to_string term) )
(* test
val term = ``((\x. x) = f) ==> (f x = x)``;
val abs = ``\x.x``;
*)

fun fun_conv_subl absl term =
  case absl of
    [] => raise UNCHANGED
  | abs :: m => ((fun_conv_sub abs) THENC (fun_conv_subl m)) term

(* test 
show_assums :=  true;
val abs = ``\x y . x + y``;
val term = ``(P (\x y. x + y) (\y.y)):bool``;
fun_conv_sub abs term;
*)

fun fun_conv_quant term =
  let val absl = find_bound_abs term in
    STRIP_QUANT_CONV (fun_conv_subl absl) term
  end
(* test 
show_assums :=  true;
val term = ``!z. (P (\x. x + z)):bool``;
fun_conv_quant_aux term;
*)



(* term of type bool *)
(* don't replace nested abstraction yet *)
fun fun_conv_aux term = 
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connector term of
      Forall => ((STRIP_QUANT_CONV fun_conv_aux) THENC fun_conv_quant) term
    | Exists => ((STRIP_QUANT_CONV fun_conv_aux) THENC fun_conv_quant) term        
    | _ => COMB_CONV fun_conv_aux term
    )
  | Abs => raise UNCHANGED

fun fun_conv term =
  let val absl = find_free_abs term in
    (fun_conv_aux THENC (fun_conv_subl absl)) term
  end

(* test 
val term = ``P (\x. x + 1) (\y.y) /\ !x. Q (\z. z + x)``;
val term = ``P (\x z. x + z):bool``; (* error to be fixed *)
val term = ``P (\x. (x = \z.z) ):bool`` ;
val abs = ``\x z. x + z``;
fun_conv term;
fun_conv_sub abs term;
find_free_abs term ;
*)
(* END FUN CONV *)

(* APP CONV *)   
(* can't print that *)
(* only do this conv if it is not first order *)
fun app_def appname subterm =
  let val (operator,arg) = dest_comb subterm in  
  (* app *)
  let val ty = type_of operator in
  let val appty = mk_type ("fun",[ty,ty]) in  
  let val app = mk_var (appname,appty) in
  (* operator *)
  let val newoperator = mk_var ("f",type_of operator) in
  (* arg *)
  let val newarg = mk_var ("x",type_of arg) in
  (* term *)
  let val t0 = list_mk_comb (app,newoperator :: [newarg]) in 
  let val t1 = mk_eq (t0,mk_comb (newoperator,newarg)) in
  let val t2 = list_mk_forall ([newoperator,newarg],t1) in
    t2
  end end end end end
  end end end end 
  handle _ => raise CONV_ERR "app_def" ""

(* test
show_assums :=  true;
val subterm = ``f a b c``;
*)

(* subterm is just a combination *)
fun app_conv_sub appname subterm =
  let val (operator,arg) = dest_comb subterm in  
  let val th1 = ASSUME (app_def appname subterm) in
  let val th2 = SPECL [operator,arg] th1 in
  let val th3 = SYM th2 in
    th3
  end end end end
  handle _ => raise CONV_ERR "app_conv_sub" ""

(* test
show_assums :=  true;
val term = ``(f a b = 2) /\ (f a = g)``;

*)

fun app_conv appname term = 
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connector term of  
      Conj => BINOP_CONV (app_conv appname) term 
    | Disj => BINOP_CONV (app_conv appname) term 
    | Neg => RAND_CONV (app_conv appname) term
    | Imp_only => BINOP_CONV (app_conv appname) term 
    | Forall => STRIP_QUANT_CONV (app_conv appname) term
    | Exists => STRIP_QUANT_CONV (app_conv appname) term    
    | App => 
      let val (operator,argl) = strip_comb term in
      case termstructure operator of
        Numeral => raise CONV_ERR "app_conv" "numeral"
      | Var =>  ((RATOR_CONV (app_conv appname)) THENC
                 (RAND_CONV (app_conv appname)) THENC
                 app_conv_sub appname) 
                term
      | Const => 
        (
        case nodeconst term of
          Eq => BINOP_CONV (app_conv appname) term 
        | Add =>  BINOP_CONV (app_conv appname) term 
        | Minus =>  BINOP_CONV (app_conv appname) term 
        | Mult =>  BINOP_CONV (app_conv appname) term 
        | Less =>  BINOP_CONV (app_conv appname) term 
        | Greater =>  BINOP_CONV (app_conv appname) term 
        | Geq =>  BINOP_CONV (app_conv appname) term 
        | Leq =>  BINOP_CONV (app_conv appname) term 
        | Newnodeconst => 
          ((RATOR_CONV (app_conv appname)) THENC
           (RAND_CONV (app_conv appname)) THENC
           app_conv_sub appname) 
          term
        )
      | Comb => ((RATOR_CONV (app_conv appname)) THENC
                 (RAND_CONV (app_conv appname)) THENC
                 app_conv_sub appname) 
                term
      | Abs => raise CONV_ERR "app_conv" "abs" 
      end   
    )      
  | Abs => raise CONV_ERR "app_conv" "abs" 

(* test
val term = ``(f a b = 2) /\ (f a = g)``;
 *)

(* DEFINE CONV *)
fun define_conv def =
  let val (bvl,t) = strip_forall def in
  (* one way *)
  let val th11 = ASSUME def in
  let val th12 = SPECL bvl th11 in
  let val th13 = repeatchange ABS (rev bvl) th12 in
  let val th14 = rewrite_conv (LAND_CONV eta_conv) th13 in 
  let val th15 = DISCH def th14 in
  (* otherway *)
  let val th21 = ASSUME (concl th14) in
  let val th22 = list_ap_thm th21 bvl in
  let val th23 = rewrite_conv beta_conv th22 in
  let val th24 = GENL bvl th23 in
  let val th25 = DISCH (concl th14) th24 in
  (* together *)
    IMP_ANTISYM_RULE th15 th25
  end end end end end 
  end end end end end
  end
  handle _ => raise CONV_ERR "define_conv" ""
(* test
val def = ``!x y. app x y = x y``;
val def = ``!x. app x  = x ``;
vval th2 = MK_ABS th1;
define_conv def;
*)



end
