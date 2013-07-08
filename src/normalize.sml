structure normalize :> normalize =
struct

(*
load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
show_assums := true; 
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
Cnf   
Intro of skolem constant (suppose it's already in normal form) 
Clauses 

Use different variables name to prevent Hol from renaming them
At least , memorise them into list so that they can be printed differently
*)

open HolKernel normalForms 
     listtools mydatatype extractvar extracttype

fun NORMALIZE_ERR function message =
    HOL_ERR{origin_structure = "normalize",
	    origin_function = function,
            message = message}

(* tools *)
fun is_logical term =
  is_conj term orelse
  is_disj term orelse   
  is_neg term orelse   
  is_imp_only term orelse
  is_forall term orelse  
  is_exists term orelse  
  is_exists1 term orelse
  is_cond term 
  
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)
fun is_new_axiom terml axiom = not (is_member (concl axiom) terml)
fun isnot_var term = not (is_var term)
fun is_var_or_const term = is_var term orelse is_const term
fun isnot_logical term = not (is_logical term)
fun has_boolty term = (type_of term = ``:bool``)

fun is_member_aconv t l =
  case l of
    [] => false
  | a :: m => aconv t a orelse is_member_aconv t m  

fun erase_double_aconv l =
 case l of
   [] => []
 | a :: m => if is_member_aconv a m
             then erase_double_aconv m
             else a :: erase_double_aconv m
             

fun is_member_aconv_arity (term,arity) termal =
  case termal of
     [] => false
  | (t,a) :: m => (aconv term t andalso arity = a) 
                  orelse is_member_aconv_arity (term,arity) m  

fun erase_double_aconv_arity termal =
 case termal of
   [] => []
 | (t,a) :: m => if is_member_aconv_arity (t,a) m
                 then erase_double_aconv_arity m
                 else (t,a) :: erase_double_aconv_arity m             

fun is_predicate term = (* not used *)
  has_boolty term andalso
  isnot_logical term andalso 
  is_comb term

fun strip_quant term =
  case connective term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise NORMALIZE_ERR "strip_quant" "" 
  
fun bound_by_quant subterm term =
 let val (bvl,t) = strip_quant term in 
   free_in subterm t andalso not (free_in subterm term)
 end  
 
fun name_strl_aux str n = 
  case n of
    0 => []
  | n => if n < 0 then raise NORMALIZE_ERR "name_strl" ""
         else str ^ (Int.toString n) :: name_strl_aux str (n - 1)

fun name_strl str n = rev (name_strl_aux str n)

fun list_mk_var (strl,tyl) = map mk_var (combine (strl,tyl))

fun rewrite_conv conv thm =
  let val goal = concl thm in
  let val eqthm = conv goal in
    EQ_MP eqthm thm
  end end   
(* end tools *)

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
  is_logical subterm 
in
fun find_free_bool_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
      Forall => find_free_bool_quant term subterm
    | Exists => find_free_bool_quant term subterm   
    | Conj => find_free_bool_binop term subterm
    | Neg => find_free_bool_unop term subterm
    | Imp_only => find_free_bool_binop term subterm
    | Disj => find_free_bool_binop term subterm
    | App => 
      (
      case nodefvc subterm of
        Eq => if has_boolty (rand subterm)
                 then find_free_bool_binop term subterm
                 else
                   filter (is_interesting_in term) [lhand subterm,rand subterm] 
                   @
                   find_free_bool_binop term subterm               
      | _ => let val (operator,argl) = strip_comb subterm in
               filter (is_interesting_in term) argl @
               find_free_bool_list term (operator :: argl)
             end
      )
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
 
fun find_free_bool term = find_free_bool_aux term term 
(* bound *)     
local fun is_interesting_in term subterm =  
  bound_by_quant subterm term andalso
  is_logical subterm 
in
fun find_bound_bool_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
      Forall => find_bound_bool_quant term subterm
    | Exists => find_bound_bool_quant term subterm   
    | Conj => find_bound_bool_binop term subterm
    | Neg => find_bound_bool_unop term subterm
    | Imp_only => find_bound_bool_binop term subterm
    | Disj => find_bound_bool_binop term subterm
    | App => 
      (
      case nodefvc subterm of
        Eq => if has_boolty (rand subterm)
                 then find_bound_bool_binop term subterm
                 else
                   filter (is_interesting_in term) [lhand subterm,rand subterm] 
                   @
                   find_bound_bool_binop term subterm               
      | _ => let val (operator,argl) = strip_comb subterm in
               filter (is_interesting_in term) argl @
               find_bound_bool_list term (operator :: argl)
             end
      )
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
   
fun find_bound_bool term = find_bound_bool_aux term term

(* SUBS is bad unless you really know what you are doing *)
(* term should have type bool *)
fun bool_conv_sub boolterm term =
  (* term *)
  (* b should be a fresh variables *)
  let val boolv = mk_var ("b",bool) in
  let val t1 = mk_eq (mk_eq (boolv,T),boolterm) in (* ((b = true) = f x) *)
  (* lemma *)
  let val eqth1 = SYM (ASSUME t1) in
  let val eqth2 = RAND_CONV bool_EQ_CONV (concl eqth1) in
  let val eqth3 = EQ_MP eqth2 eqth1 in
  (* first part  *)
  let val th11 = ASSUME term in
  let val th12 = SUBS [eqth3] th11 in (* to be checked *)
  let val th13 = DISCH (hd (hyp eqth3)) th12 in
  let val th14 = GEN boolv th13 in
  let val th15 = DISCH_ALL th14 in
  (* second part *)
  let val th21 = ASSUME (concl th14) in
  let val th22 = SPEC boolterm th21 in (* to be checked *)
  let val t2 = lhs (lhand (concl th22)) in
  let val eqth4 = bool_EQ_CONV t2 in
  let val th23 = MP th22 eqth4 in
  let val th24 = DISCH_ALL th23 in
  (* together *)
    IMP_ANTISYM_RULE th15 th24
  end end end end end 
  end end end end end 
  end end end end end
  end 

(* test
val boolterm = ``!f:num -> bool . f x``;
val term = ``P (!f:num -> bool . f x) (!f:num -> bool . f x): bool``;
bool_conv_sub term boolterm;
*)
fun bool_conv_subl boolterml term = 
  case boolterml of
    [] => raise UNCHANGED
  | boolterm :: m => ((bool_conv_sub boolterm) THENC (bool_conv_subl m)) term
  
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
    case connective term of
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
val boolterml = find_free_bool term;
val boolterml2 = find_bound_bool term;
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
(* END BOOL CONV *)

(* NUM CONV *)

(* find *)
local fun is_interesting_in term subterm = 
  has_numty subterm andalso 
  free_in subterm term andalso 
  not (numSyntax.is_numeral term)
in
fun find_free_num term =  
  erase_double_aconv (find_terms (is_interesting_in term) term) 
end

(* term should start with a quantifier *)  
local fun is_interesting_in term subterm = 
  bound_by_quant subterm term andalso
  has_numty subterm 
(* a numeral can't be bound so don't need to exclude it *)  
in 
fun find_bound_num term =  
  erase_double_aconv (find_terms (is_interesting_in term) term) 
end  
(* end find *)

(* term should be of type bool *)
fun num_axiom term = 
  let val axiom = arithmeticTheory.ZERO_LESS_EQ in
    SPEC term axiom
  end

fun num_conv_subl fterml term =
  if has_boolty term
  then
    let val axioml1 = map num_axiom fterml in
    (* check if any of the axiom is already there in the top conjunction 
       and remove it *)
    let val terml = strip_conj term in
    let val axioml2 = filter (is_new_axiom terml) axioml1 in
      if null axioml2
      then 
        raise UNCHANGED
      else   
        let val axiom1 = LIST_CONJ axioml2 in
        (* first part *)
        let val th11 = ASSUME term in
        let val th12 = CONJ axiom1 th11 in  
        let val th13 = DISCH_ALL th12 in  
        (* second part *) 
        let val th21 = ASSUME (mk_conj (concl(axiom1),term)) in
        let val th22 = CONJUNCT2 th21 in
        let val th23 = DISCH_ALL th22 in
        (* together *)
        IMP_ANTISYM_RULE th13 th23  
        end end end end end end end
    end end end 
  else raise UNCHANGED
 
(* test
 num_conv_subl [``y:num``] ``(0 ≤ y) /\ (?x:num . (y:num) = (y:num))``;
 num_conv_subl [``y:num``,``x:num``] ``(0 ≤ y) /\ (?x:num . (y:num) = (y:num))``;
*)  

(* to be rewritten *)
fun num_conv_forall_imp term =
  let val (bvl,t) = strip_forall term in
  let val numbvl = filter has_numty bvl in
  let val axioml1 = map num_axiom numbvl in
  let val (term1,term2) = dest_imp_only t in
  let val terml = strip_conj term1 in
  let val axioml2 = filter (is_new_axiom terml) axioml1 in
    if null axioml2
    then 
      raise UNCHANGED
    else     
      let val axiom1 = LIST_CONJ axioml2 in
      let val taxiom = concl axiom1 in
      let val tconj = mk_conj (taxiom,term1) in
      (* first part *)
      let val th11 = ASSUME term in
      let val th12 = SPEC_ALL th11 in
      let val th13 = ADD_ASSUM taxiom th12 in
      let val th14 = UNDISCH th13 in 
      (* some lemma *)
      let val lemma11 = ASSUME tconj in
      let val lemma12 = CONJUNCT1 lemma11 in
      let val lemma13 = CONJUNCT2 lemma11 in
      let val lemma14 = PROVE_HYP lemma12 th14 in
      let val lemma15 = PROVE_HYP lemma13 lemma14 in
      let val lemma16 = DISCH tconj lemma15 in
      (* end *)
      let val th15 = GENL bvl lemma16 in
      let val th16 = DISCH_ALL th15 in
      (* second part *)
      let val th21 = ASSUME (list_mk_forall (bvl,mk_imp (tconj,term2))) in
      let val th22 = SPEC_ALL th21 in
      let val th23 = UNDISCH th22 in 
      (* some lemma *) 
      let val lemma1 = ASSUME term1 in
      let val lemma2 = CONJ axiom1 lemma1 in
      (* end *)  
      let val th24 = PROVE_HYP lemma2 th23 in
      let val th25 = DISCH term1 th24 in
      let val th26 = GENL bvl th25 in
      let val th27 = DISCH_ALL th26 in
      (* regroup *)
        IMP_ANTISYM_RULE th16 th27
      end end end end end 
      end end end end end 
      end end end end end 
      end end end end end
      end end end end 
  end end end 
  end end end

(* test 
val term = ``!(x:num) (y:num). A:bool ==> (x + y + z = 0)``;
REPEATC num_conv_forall_imp term;  
*)


(* second function *)
fun num_conv_forall_noimp term =
  let val (bvl,t) = strip_forall term in
  let val numbvl = filter has_numty bvl in
  let val axioml1 = map num_axiom numbvl in
    if null axioml1
    then 
      raise UNCHANGED
    else     
      let val axiom1 = LIST_CONJ axioml1 in
      let val tconj = concl (axiom1) in
      (* first part *)
      let val th11 = ASSUME term in
      let val th12 = SPEC_ALL th11 in
      let val th13 = ADD_ASSUM tconj th12 in
      let val th14 = DISCH tconj th13 in 
      let val th15 = GENL bvl th14 in
      let val th16 = DISCH_ALL th15 in
      (* second part *)
      let val th21 = ASSUME (list_mk_forall (bvl,mk_imp (tconj,t))) in
      let val th22 = SPEC_ALL th21 in
      let val th23 = UNDISCH th22 in 
      let val th24 = PROVE_HYP axiom1 th23 in
      let val th25 = GENL bvl th24 in
      let val th26 = DISCH_ALL th25 in
      (* regroup *)
        IMP_ANTISYM_RULE th16 th26
      end end end end end 
      end end end end end 
      end end end end 
  end end end
 
(* test 
val term = ``!(x:num) (y:num). (x + y + z = 0)``;
num_conv_forall_noimp term;  
*) 

       
  
(* test
show_assums := true ;
val term = ``!x y. (x = 0) /\ (y = 0) ``;
num_conv_forall_bt [``x:num``] term; 
*)
fun num_conv_quant term =
  let val terml = find_bound_num term in
    STRIP_QUANT_CONV (num_conv_subl terml) term
  end

(* num conv forall *) 
fun num_conv_forall_aux term =
  let val (bvl,t) = strip_forall term in
    if is_imp_only t
    then
      num_conv_forall_imp term
    else
      num_conv_forall_noimp term
  end      

fun num_conv_forall term =
  let val terml1 = find_bound_num term in
  let val terml2 = filter isnot_var terml1 in
    (num_conv_quant THENC num_conv_forall_aux) term
  end end
 
(* test
val term = ``!x y. (x = 0) /\ (y = 0) /\ (z = 0) /\ (f (y:num) = 0)``;
num_conv_forall_all term term; 
*)

(* num_conv_exists *)
fun num_conv_exists term =
  let val terml = find_bound_num term in
    STRIP_QUANT_CONV (num_conv_subl terml) term  
  end 

(* test
val term = ``?x y. (x = 0) /\ (y = 0) /\ (z = 0) /\ (f (y:num) = 0)``;
num_conv_exists_all term; 
*)

(* main function traverses the term *)
fun num_conv_aux term =   
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connective term of
      Forall => ((STRIP_QUANT_CONV num_conv_aux) THENC num_conv_forall) term
    | Exists => ((STRIP_QUANT_CONV num_conv_aux) THENC num_conv_exists) term        
    | _ => COMB_CONV num_conv_aux term
    )
  | Abs => raise NORMALIZE_ERR "num_conv" "abstraction"

fun num_conv term =
  let val terml = find_free_num term in
    (num_conv_aux THENC (num_conv_subl terml)) term
  end
  
(* test
val term = ``(a = 0) /\ ?x y. (x = 0) /\ (!(x:num) z. x = f z) /\ (f (y:num) = 0)``;
num_conv term; 
*)
(* END NUM CONV *)

(* FUN CONV *)  
(* find *)
fun find_free_abs_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
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
    case connective subterm of
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
(* end tools *)
  
fun ap_thml thm terml =
  case terml of
    [] => thm 
  | t :: m => ap_thml (AP_THM thm t) m 

fun list_fun_eq_conv vl term =
  case vl of
    [] => raise UNCHANGED
  | [v] => X_FUN_EQ_CONV v term
  | v :: m => ((X_FUN_EQ_CONV v) THENC 
              (STRIP_QUANT_CONV (list_fun_eq_conv m))) 
              term 

(* input is ``f = \x y. x + y`` *)
fun fun_axiom term =
  let val funv = lhs term in
  let val abst = rhs term in
  let val (bvl,t) = strip_abs abst in
  (* useful axiom *)
  let val axiom1 = list_fun_eq_conv bvl term in
  let val axiom2 = REFL abst in
  let val axiom3 = ap_thml axiom2 bvl in
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
(* test 
show_assums := true;
val term = ``f = \x y. x + y``;
fun_axiom term;
*)

(* term should have type bool *)
fun fun_conv_sub abs term =
  (* term *)
  let val ty = type_of abs in
  let val v = mk_var ("f",ty) in
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
    case connective term of
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
(* returns a list of (term,lowestarity) *)
fun find_free_app_aux termal term subterm  = 
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
      Forall => find_free_app_quant termal term subterm
    | Exists => find_free_app_quant termal term subterm   
    | Conj => find_free_app_binop termal term subterm
    | Neg => find_free_app_unop termal term subterm
    | Imp_only => find_free_app_binop termal term subterm
    | Disj => find_free_app_binop termal term subterm
    | App => 
      let val (operator,argl) = strip_comb subterm in
      let val arity = length argl in
        case termstructure operator of
          Numeral => []
        | Var => if free_in subterm term
                 then 
                   let val lowestarity = lookup operator termal in
                     if arity > lowestarity
                     then
                       (subterm,lookup operator termal) ::  
                       find_free_app_list termal term (operator :: argl)
                     else 
                       find_free_app_list termal term (operator :: argl)
                   end    
                 else 
                   find_free_app_list termal term (operator :: argl)
        | Const => 
                 if free_in subterm term
                 then 
                   let val lowestarity = lookup operator termal in
                     if arity > lowestarity
                     then
                       (subterm,lookup operator termal) ::  
                       find_free_app_list termal term (operator :: argl)
                     else 
                       find_free_app_list termal term (operator :: argl)
                   end
                 else 
                   find_free_app_list termal term (operator :: argl)        
        | Comb => raise NORMALIZE_ERR "find_free_app_aux" "comb"
        | Abs => raise NORMALIZE_ERR "find_free_app_aux" "abstraction"
      end end
    )         
  | Abs => raise NORMALIZE_ERR "find_free_app_aux" "abstraction"
and find_free_app_list termal term subterml =
  List.concat (map (find_free_app_aux termal term) subterml)
and find_free_app_quant termal term subterm =
  let val (bvl,t) = strip_quant subterm in
    find_free_app_aux termal term t
  end  
and find_free_app_binop termal term subterm =
  find_free_app_list termal term [lhand subterm,rand subterm] 
and find_free_app_unop termal term subterm =
  find_free_app_aux termal term (rand subterm)

fun find_free_app term = 
  let val termal = collapse_lowestarity (get_fvcal (extract_var term)) in
    erase_double_aconv_arity (find_free_app_aux termal term term)
  end
  
(* term should be a quantifier *)
fun find_bound_app_aux term subterm = 
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
      Forall => find_bound_app_quant term subterm
    | Exists => find_bound_app_quant term subterm   
    | Conj => find_bound_app_binop term subterm
    | Neg => find_bound_app_unop term subterm
    | Imp_only => find_bound_app_binop term subterm
    | Disj => find_bound_app_binop term subterm
    | App => 
      let val (operator,argl) = strip_comb subterm in
        case termstructure operator of
          Numeral => []
        | Var => if bound_by_quant subterm term 
                 then
                   (subterm,0) ::  
                   find_bound_app_list term (operator :: argl)
                 else 
                   find_bound_app_list term (operator :: argl)
        | Const => if bound_by_quant subterm term 
                   then
                     (subterm,0) ::  
                     find_bound_app_list term (operator :: argl)
                   else 
                     find_bound_app_list term (operator :: argl)              
        | Comb => raise NORMALIZE_ERR "find_bound_app_aux" "comb"
        | Abs => raise NORMALIZE_ERR "find_bound_app_aux" "abstraction"
      end 
    )           
  | Abs => raise NORMALIZE_ERR "find_bound_app_aux" "abstraction"
and find_bound_app_list term subterml =
  List.concat (map (find_bound_app_aux term) subterml)
and find_bound_app_quant term subterm =
  let val (bvl,t) = strip_quant subterm in
    find_bound_app_aux term t
  end  
and find_bound_app_binop term subterm =
  find_bound_app_list term [lhand subterm,rand subterm] 
and find_bound_app_unop term subterm =
  find_bound_app_aux term (rand subterm)

fun find_bound_app term = erase_double_aconv_arity (find_bound_app_aux term term)

fun app_def term =
  let val (operator1,argl1) = strip_comb term in
  let val opty = type_of operator1 in
  let val operator = mk_var ("f",opty) in
  let val argtyl = map type_of argl1 in
  let val n = length argl1 in
  let val strl = name_strl "x" n in
  let val argl = list_mk_var (strl,argtyl) in
  let val appty = mk_type ("fun",[opty,opty]) in  
  let val app = mk_var ("app",appty) in
  let val term = list_mk_comb (operator,argl) in 
  let val t1 = list_mk_comb (app,operator :: argl) in
  let val t2 = mk_eq (t1,term) in
  let val t3 = list_mk_forall (operator :: argl,t2) in
    t3
  end end end end end
  end end end end end
  end end end



(* operator is a subterm that appears free in term but with wrong arity *) 
(* P [ f a , f a b ]  <----> 
  !app. (!x. app (f x) = (f x) ) =>  P [f a, app (f a) b] *)
(*
One way
|- P [ f a , f a b ]
!x. app (f x) = (f x)  |- !x. app (f x) = (f x) 
!x. app (f x) = (f x)  |- app (f a) = (f a) 
COMB_CONV val th14 = SUBS [th13] th11
|- (f a) b = app (f a) b
try to use subst here
!x. app (f x) = (f x)  |-  P [f a, app (f a) b]

Other way
|- !app. (!x. app (f x) = (f x) ) =>  P [f a, app (f a) b]
|- (!x. app (f x) = (f x) ) =>  P [f a, app (f a) b]
(!x. app (f x) = (f x) ) |- P [f a, app (f a) b]
SUBS multiple subs possible 
(!x. app (f x) = (f x) ) |- app (f a) b = f b 
(!x. app (f x) = (f x) ) |- P [f a, (f a) b]

*)
(* use SUBST to replace selected occurences *)
(* make a new fresh variables each time you do that *)

(* app is not local *)
fun dest_comb_nb (term,nb) =
  if nb = 0 then (term,[])
else 
  if nb > 0 then let val (operator,arg) = dest_comb term in
                 let val (rest,resnb) = dest_comb_nb (operator,nb - 1) in
                   (rest,resnb @ [arg])
                 end end 
else 
  raise NORMALIZE_ERR "" ""

fun get_arity term = length (snd (strip_comb term))

fun app_conv_sub (subterm,lowestarity) term =
  let val arity = get_arity subterm in
  let val (operator,argl) = dest_comb_nb (subterm,arity - lowestarity) in  
  let val (operator1,argl1) = strip_comb operator in
  (* preparation *)
  let val lemma1 = ASSUME (app_def operator) in
  let val lemma2 = SPECL (operator1 :: argl1) lemma1 in
  let val lemma3 = ap_thml lemma2 argl in
  let val lemma4 = SYM lemma3 in
  (* first part *)
  let val th11 = ASSUME term in 
  let val th12 = SUBS [lemma4] th11 in (* to be checked *)
  let val th13 = DISCH term th12 in
  (* second part *)
  let val th21 = ASSUME (concl th12) in
  let val th22 = SUBS [lemma3] th21 in (* to be checked *)
  let val th23 = DISCH (concl th12) th22 in
    IMP_ANTISYM_RULE th13 th23 
  end end end end end
  end end end end end
  end end end 
  

 
(* same problem *) (* need to generalize app *)

fun app_conv_subl subtermal term =
  case subtermal of
    [] => raise UNCHANGED
  | subterma :: m => ((app_conv_sub subterma) THENC (app_conv_subl m)) term


fun app_conv_quant term =
  let val subtermal = find_bound_app term in
    STRIP_QUANT_CONV (app_conv_subl subtermal) term
  end
(* test 
show_assums :=  true;
val term = ``!z. (P (\x. x + z)):bool``;
app_conv_quant_aux term;
app_conv term;
*)

(* term of type bool *)
(* don't replace nested subtermatraction yet *)
fun app_conv_aux term = 
  case termstructure term of
    Numeral => raise UNCHANGED 
  | Var => raise UNCHANGED  
  | Const => raise UNCHANGED
  | Comb => 
    (
    case connective term of
      Forall => ((STRIP_QUANT_CONV app_conv_aux) THENC app_conv_quant) term
    | Exists => ((STRIP_QUANT_CONV app_conv_aux) THENC app_conv_quant) term        
    | _ => COMB_CONV app_conv_aux term
    )
  | Abs => raise UNCHANGED (* do not go under abstraction *) 


fun app_conv term =
  let val subtermal = find_free_app term in
    (app_conv_aux THENC (app_conv_subl subtermal)) term
  end

 (* test
val term = ``((f:num -> num -> num -> num ) a = g) 
             /\ ((f:num -> num -> num -> num)  a b c = h)``
val subterm = ``(f:num -> num -> num -> num)  a b c``;
val lowestarity = 1;
val subtermal = find_free_app term;
app_conv_sub (subterm,1) term;

app_conv term;
app_cfun_conv term;onv term;
app_conv_subl subtermal term;
*)
(* post thinking : two app of the same type output should have the same name
   two app of the same type output comes from the same type and arity *)
   
(* END APP CONV *)

(* SKOLEM REWRITE *)
(* 
[?x. P x,..] |-  F
*)
(*
val var = mk_var ("x",``:num``);
val hypterm = ``?x. x = 0``;
val thm = mk_thm ([hypterm],F);
val hypterm = ``x = 0``;
show_assums := true;
val varl = [var];
*)
(* thm should have conclusion set to false *)
(* normally it's not bad to specify with their own names 
since they do not appear free in hypothesis maybe *)
fun skolem_rewrite varl hypterm thm =
  let val th1 = DISCH hypterm thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = NOT_EXISTS_CONV (concl th2) in
  let val th4 = EQ_MP th3 th2 in
  let val th5 = SPECL varl th4 in
  let val th6 = NOT_ELIM th5 in
  let val th7 = UNDISCH th6 in
    th7
  end end end end end 
  end end

fun skolem_rewrite_rev varl hypterm thm =
  let val th1 = DISCH hypterm thm in
  let val th2 = NOT_INTRO th1 in
  let val th3 = GENL varl th2 in
  let val th4 = FORALL_NOT_CONV (concl th3) in
  let val th5 = EQ_MP th4 th3 in
  let val th6 = NOT_ELIM th5 in
  let val th7 = UNDISCH th6 in
    th7
  end end end end end 
  end end
  (* END SKOLEM REWRITE *)

(* CLAUSE CONV *)
(* input: a term !x y. A[x,y] /\ B[x,y] *)   
(*
  forall_and conversion

  then
  remove useless quantifier
   x doesn't appear free in A then !x is useless.
 *) 

(* output: [!x y. A[x,y], !x y. B[x,y]] *)
(* set of clauses *)

(* END CLAUSE CONV *)  

end