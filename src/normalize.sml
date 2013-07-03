structure normalize :> normalize =
struct

(*

load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
show_assums := true; 
*)

open HolKernel normalForms 
     listtools mydatatype extractvar 

fun NORMALIZE_ERR function message =
    HOL_ERR{origin_structure = "normalize",
	    origin_function = function,
            message = message}


(* INIT *)
  (* input is an axioml and a conjecture *)
  (* goal is not special anymore *)
  (* output: thm *)
fun unify axioml =
  let val newaxioml = map DISCH_ALL axioml in
    LIST_CONJ newaxioml
  end

  (* should maybe monomorph to itself *)
fun initial_assume axioml conjecture =
  let 
    val prop1 = concl (unify axioml) 
    val prop2 = concl (DISCH_ALL conjecture) 
  in
    ASSUME (mk_conj (prop1, mk_neg prop2))
  end
(* END INIT *)


(* BIG REWRITING *)
  (* choose bound variables names so that thec program don't have to rename them *)

(* CNF *)
  (* eliminate unused quantifier: 
  normalForms.CNF_CONV ``?x. !x. p x``; *)
  (* rewrite =>, ?! and if then else *)
  (* do beta-reduction *)
fun rewrite conv thm =
  let val goal = concl thm in
  let val eqthm = conv goal in
    EQ_MP eqthm thm
  end end
  
fun rewrite_cnf thm = rewrite (QCONV normalForms.CNF_CONV) thm
(* END CNF *)

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

fun isnot_logical term = not (is_logical term)
fun has_boolty term = (type_of term = ``:bool``)
(* use extract var to extract interesting term *)
fun is_firstorder_predicate term = 
  has_boolty term andalso
  isnot_logical term andalso 
  is_comb term

fun is_var_or_const term = is_var term orelse is_const term

fun strip_quant term =
  case connective term of
    Forall => strip_forall term
  | Exists => strip_exists term
  | _ => raise NORMALIZE_ERR "strip_quant" "" 
  
fun bound_by_quant subterm term =
 let val (bvl,t) = strip_quant term in 
   free_in subterm t andalso not (free_in subterm term)
 end  
 
(* end tools *)

(* BOOL REWRITE *)
(* extract *)  

  (* to be changed by a traverse of the tree *)
local fun is_interesting_in term subterm =  
  free_in subterm term andalso
  has_boolty subterm andalso 
  not (is_var_or_const subterm) andalso
  not (term = subterm)
in
fun find_free_bool term =
  erase_double (find_terms (is_interesting_in term) term)
end

fun find_free_bool_aux term subterm = (* term should be a boolean *)
  case termstructure subterm of
    Numeral => []
  | Var => []  
  | Const => []
  | Comb => 
    (
    case connective subterm of
    | App => 
    | Forall => let val (bvl,t) = strip_forall subterm in
                  find_free_bool_aux term t
                end  
    | Exists => let val (bvl,t) = strip_exists subterm in
                  find_free_bool_aux term t
                end      
    | Conj =>
    | Neg =>
    | Imp =>
    | Disj =>
    | Equiv =>
    
    (* don't want to write under equivalence *)
    
    | _ => let val (operator,arg) = dest_comb subterm in
             (find_free_bool_aux term operator) @ (find_free_bool_aux term arg)
           end  
    )
  | Abs => []


  (* to be changed *)
  (* term should start with a quantifier *)  
local fun is_interesting_in term subterm =  
  bound_by_quant subterm term andalso
  has_boolty subterm andalso 
  not (is_var_or_const subterm) andalso
  not (term = subterm)
in
fun find_bound_bool term =
  erase_double (find_terms (is_interesting_in term) term)
end

(* end extract *)

(* SUBS is bad unless you really know what you are doing *)
  (* term1 : P f x *)
  (* term2 : f x *)
  (* term should be of type bool *)


(* P (f x) (g (∀f. f x)) ⇔ ∀b. ((b = true) ⇔ ∀f. f x) ⇒ P (f x) (g b) *)


fun bool_conv_sub boolterm term =
  (* term construction *)
  let val boolv = mk_var ("b",bool) in
  let val t1 = mk_eq (mk_eq (boolv,T),boolterm) in (* ((b = true) = f x) *)
  (* lemma *)
  let val eqth1 = SYM (ASSUME t1) in
  let val eqth2 = RAND_CONV bool_EQ_CONV (concl eqth1) in
  let val eqth3 = EQ_MP eqth2 eqth1 in
  (* first part  *)
  let val th11 = ASSUME term in
  let val th12 = SUBS [eqth3] th11 in (* hate using SUBS *)
  let val th13 = DISCH (hd (hyp eqth3)) th12 in
  let val th14 = GEN boolv th13 in
  let val th15 = DISCH_ALL th14 in
  (* second part *)
  let val th21 = ASSUME (concl th14) in
  let val th22 = SPEC boolterm th21 in
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
val term = ``P (f x) (g !f:num -> bool . f x): bool``;
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
  let val boolterml = find_free_bool term in
    (bool_conv_aux THENC (bool_conv_subl boolterml)) term
  end

(* test
val term = ``!x. x + 1 = 0 ``;
bool_conv term; (* interesting problem *)
*)

(* TRANSLATION IDEA *)
(* 
 = :bool -->  <=> 
 = :bool -->   =  
depend on the arguments 
*)
(*
true --> $true
true --> btrue 
*)
(* END *)
(* END BOOL REWRITE *)

(* NUM REWRITE *)
(* should look at the first boolean over a subterm *)
(* term should be of type bool *)

(* tools *)
fun has_boolty term = (type_of term = ``:bool``)
fun has_numty term = (type_of term = ``:num``)

fun num_axiom term = 
  let val axiom = arithmeticTheory.ZERO_LESS_EQ in
    SPEC term axiom
  end



fun is_new_axiom terml axiom = not (is_member (concl axiom) terml)
fun isnot_var term = not (is_var term)
(* end tools *)


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
        let un num_conv_exists term =

        val th11 = ASSUME term in
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
 
(* replace terml under an abstraction *)

 
(* test
 num_conv_subl [``y:num``] ``(0 ≤ y) /\ (?x:num . (y:num) = (y:num))``;
 num_conv_subl [``y:num``,``x:num``] ``(0 ≤ y) /\ (?x:num . (y:num) = (y:num))``;
*)  

  
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
      (* regroupun num_conv_exists term =

       *)
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

(* tools *)



 
local fun is_interesting_ft term subterm = 
  has_numty subterm andalso 
  free_in subterm term andalso 
  not (numSyntax.is_numeral term)
in
fun find_free_num term =  
  erase_double (find_terms (is_interesting_ft term) term) 
end

(* term should start with a quantifier *)  
local fun is_interesting_bt term subterm = 
  bound_by_quant subterm term andalso
  has_numty subterm 
(* a numeral can't be bound so don't need to exclude it *)  
in 
fun find_bound_num term =  
  erase_double (find_terms (is_interesting_bt term) term) 
end  
(* end tools *)

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
    ((num_conv_quant_bt terml2) THENC num_conv_forall_aux) term
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
(* END NUM REWRITE *)

(* FUN REWRITE *)   (* DON'T FORGET TO TRY ETA_CONV FIRST *)

(* tools *)
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
  | Abs => if free_in subterm term
           then [subterm]
           else []   

fun find_free_abs term = find_free_abs_aux term term

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
  | Abs => if bound_by_quant subterm term
           then [subterm]
           else []   

fun find_bound_abs term = find_bound_abs_aux term term
(* end tools *)
  
  
  (* hd bvl is bad *) 
  (* term should have this form  f = \x.t *)
  (* to be upgraded to this form f = \x1x2...  .t *)
fun fun_axiom term =
  let val funv = lhs term in
  let val abst = rhs term in
  let val (bvl,t) = strip_abs abst in
  (* useful axiom *)
  let val axiom1 = X_FUN_EQ_CONV (hd bvl) term in
  let val axiom2 = UNBETA_CONV (hd bvl) t in
  (* first part *)
  let val th11 = ASSUME term in
  let val th12 = EQ_MP axiom1 th11 in 
  let val th13 = BETA_RULE th12 in
  let val th14 = DISCH_ALL th13 in 
  (* second part *)
  let val th21 = ASSUME (concl th13) in
  let val th22 = SPEC_ALL th21 in
  let val th23 = TRANS th22 axiom2 in
  let val th24 = GEN (hd bvl) th23 in  
  let val th25 = EXT th24 in
  let val th26 = DISCH_ALL th25 in
  (* together *)
    IMP_ANTISYM_RULE th14 th26
  end end end end end
  end end end end end
  end end end end end
  
(* test 
show_assums := true;
val term = ``f = \x.x + 1``;
fun_axiom term;
*)

(* same problem with names *)
(* abs is just a sub term *)
(* abs shouldn't not contain any sub abstraction because of the use of betarule *)
fun fun_conv_sub abs term =
  if has_boolty term
  then
    (* term *)
    let val ty = type_of abs in
    let val v = mk_var ("f",ty) in
    let val t1 = mk_eq (v,abs) in   
    let val (bv,t2) = dest_abs abs in
    (* axiom *)
    let val axiom1 = fun_axiom t1 in
    let val (axiom2,axiom3) = EQ_IMP_RULE axiom1 in
    let val axiom4 = REFL t2 in
    let val axiom5 = GEN bv axiom4 in
    let val lemma1 = UNDISCH axiom2 in
    let val lemma2 = UNDISCH axiom3 in
    (* first part *)
    let val th11 = ASSUME term in
    let val th12 = SYM (ASSUME t1) in  
    let val th13 = SUBS [th12] th11 in  
    let val th14 = PROVE_HYP lemma2 th13 in
    let val th15 = DISCH (concl lemma1) th14 in
    let val th16 = GEN v th15 in
    let val th17 = DISCH_ALL th16 in
    (* second part *) 
    let val th21 = ASSUME (concl th16) in
    let val th22 = SPEC abs th21  in
    let val th23 = BETA_RULE th22 in (* to be changed to be more general *)
    let val th24 = MP th23 axiom5 in
    let val th25 = DISCH_ALL th24 in 
    (* together *)
      IMP_ANTISYM_RULE th17 th25 
    end end end end end 
    end end end end end 
    end end end end end 
    end end end end end 
    end end
  else raise UNCHANGED

fun fun_conv_subl absl term =
  case absl of
    [] => raise UNCHANGED
  | abs :: m => ((fun_conv_sub abs) THENC (fun_conv_subl m)) term

(* test 
show_assums :=  true
val abs = ``\x. x + 1``;
val term = ``(P (\x. x + 1) (\y.y)):bool``;
fun_conv_sub abs term;
*)

(* do not go under abstraction *)
(* contradictory with beta rule *)
(* nested abstraction is the problem *)
fun fun_conv_quant term =
  let val absl = find_bound_abs term in
    STRIP_QUANT_CONV (fun_conv_subl absl) term
  end
(* test 
show_assums :=  true;
val term = ``!z. (P (\x. x + z)):bool``;
fun_conv_quant_aux term;
*)

(* not efficient *) 


(* term of type bool *)
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
  let val absl = find_free_abs term term in
    (fun_conv_aux THENC (fun_conv_subl absl)) term
  end

(* test 
val term = ``P (\x. x + 1) (\y.y) /\ !x. Q (\z. z + x)``;
val term = ``P (\x z. x + z):bool``; (* error to be fixed *)
fun_conv term;
*)


(* END FUN REWRITE *)


(* APP REWRITE *)   

(* if some function appears with different arguments then *)  
(* bounded function appears with lowest_arity equal to 0 *)
(* Same definition as let *)

(* input: a comb term *) 
(* app should supports multiple arguments *)
fun (make_appassume:conv) operator =
  let val ty = mk_type ("fun", [type_of operator,type_of operator]) in
  let val app = mk_var ("app", ty) in    
  let val appdeflhs =  mk_abs (operator, operator) in
  let val appdef = mk_eq (app, appdeflhs) in  
  let val assume = ASSUME appdef in
    assume
  end end end end end
 
(* 
app = \f. f |- app = \f. f 
app = \f. f |- app f = (\f. f) f 
app = \f. f |- app f = f
app = \f. f |- f = app f
*)
(* f = g can be rewrite !x f x = g x *) FUN_CONV

(* if f is a function that's not right *)
(* need to beta_conv or cnf_conv the result *)
(* basic conversion *)

(* no dict for now but to be added later *)
fun app_var_conv var =
  let val assume = make_appassume var in
  let val thm1 = AP_THM assume var in
  let val thm2 = DEPTH_CONV BETA_CONV (concl thm1) in
  let val thm3 = EQ_MP thm2 thm1 in 
    SYM thm3
  end end end end
  handle _ => raise UNCHANGED (* maybe not neccesary *)
  
  
app_var_conv ``f x``;
(* there can be deeply nested application *)
(* dict contains bounded variables and free variables *)
fun app_noquant_conv term = DEPTH_CONV app_var_conv term

fun app_cnf_conv term = STRIP_QUANT_CONV app_noquant_conv term
app_cnf_conv ``!f. f (!x.x)``;

(*
show_assums := true;
make_appassume ``f : num -> num -> num``;
val thm = make_appthm ``f : num -> num -> num``;
STRIP_QUANT_CONV make_appthm ``!f. f``;
*)


(* doesn't create boolean arguments *)
(* doesn't add new type *)
(* maybe last thing to do *)
(* input is a first order formula with no lambda abstraction
   in cnf form ? ! ....
   
fun rewrite_app1 thm =  
  (* strip first existential and forall quantifier *)
 

(*
val thm1 = ASSUME ``x:num = x`` ;
val thm2 = ASSUME ``?!x. x = 0``;
val thm3 = SELECT_AX;
val thm4 = EXISTS_UNIQUE_DEF;
val assume = initial_assume [thm1,thm2] thm3;
val nf = normalform assume;
*)






(* END APP REWRITE *)





  
(* INSIDE BEAGLE *)
(* 
REDEPTH_CONV  
normalForms.SKOLEMIZE_CONV ``!y. (f = \x. g x) /\ (?f. f x = (\x.x) 2)``;
``!y. (?f. f x = 2)``
*)


(* let's try to define this conversion in hol term *)

(* should also add the num_axiom for free variables and bound variables *)  
(* |- x: num >= 0 *)

(* TYPE DICTIONNARY *)



fun 
f x y /\ f x = g

(* every thing is mixed up now *)
(* post thinking : two app of the same type output should have the same name *)
   two app of the same type output comes from the same type and arity *)
(* dictionnary should contain arity start from 2 )
free variables have specific names important names

app1 (f x) y /\ f x = g


f x y = app2 (f x) y


(* add the app function *)
   (* create a ty dict *)
   (* create the app dict *)
   

Need to look at beagle code internally

For all 
beagle does skolemisation but I need to understand a very simple thing about it.
!x . x = 0 becomes x = 0
For_all elimination


?y . !x.
(* difficulty there (what beagle does?)*)

 |-  x = 0


  
  
  
  (*
DISCH_ALL
|- B1  |- B2   
LIST_CONJ
|- B1 /\ B2
mk_thm [
Which prove that C |- D

Prove that (( (-A1 \/ B1) /\ ......./\ C /\ -D) |- F
(( (A1 ==> B1) /\ ......./\ C /\ -D) |- (( (-A1 \/ B1) /\ ......./\ C /\ -D) 
C |- D holds

REDEPTH_CONV BETA_CONV ``?y. (f = \x. g x) /\ (!f. f x = (\x.x) 2)``;
REDEPTH_CONV ETA_CONV ``(\x.f x) = g``;

CNF_CONV ``?y. (f = \x. g x) /\ (!f. f x = (\x.x) 2)``;
normalForms.CNF_CONV ``(P (?!x . f x = ((\x.x) 2))) /\ (x = 2)``; 
(* does beta reduction *)
(* does normal form first order *)
   (* does skolemisation *)
  
  
  
  
  


