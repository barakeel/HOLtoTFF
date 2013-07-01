structure normalize :> normalize =
struct

(*
load "normalForms"; open normalForms;
load "listtools"; open listtools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
*)

open HolKernel normalForms 
     listtools mydatatype extractvar 

fun NORMALIZE_ERR function message =
    HOL_ERR{origin_structure = "normalize",
	    origin_function = function,
            message = message}

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

(* BIG REWRITING *)
(* 
eliminate unused quantifier: normalForms.CNF_CONV ``?x. !x. p x``;
rewrite =>, ?! and if then else
do beta-reduction 
*)  

fun rewrite conv thm =
  let val goal = concl thm in
  let val rwthm = conv goal in
    EQ_MP rwthm thm
  end end
  
fun rewrite_cnf thm = rewrite (QCONV normalForms.CNF_CONV) thm

(* TYPE PROBLEM *)

(* if then else and ?! already replaced by CNF_CONV *)
(* don't create an abstraction *)
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

(* use extract var to extract interesting term *)
fun is_firstorder_predicate term = isnot_logical term andalso is_comb term

(* BOOL REWRITE *)

(*
bterm = b' |- bterm = b'  
bterm = b' |- P[b'] => P[bterm]
|- b' = bterm => P[b'] => P[bterm] 
|-  b' = bterm  /\ P[b'] => P[bterm]
[b' = bterm] |- P[bterm] <=> P[b']
|- P[bterm]
then rewrite
[b' = bterm] |- P[b']
undisch
|- (b' = bterm) => P[b']
b' is a free variable but variables inside bterm maybe bound
*)

 
(* problem this boolean can be bound *)
(* bound is only   let val goal = concl thm in
  let val rwthm = QCONV CNF_CONV goal in
    EQ_MP rwthm thm 
  end enda variable not a term *)
(* this problem will be solved at the end *)
(* it's in normal form *)
fun has_booltype term = (type_of term = ``:bool``)
(* input : a list of combination *)

(* output: thm*)
fun is_var_or_const term = is_var term orelse is_const term

fun is_interesting_in term subterm =  
  has_booltype subterm 
  andalso 
  not (is_var_or_const subterm) 
  andalso
  not (term = subterm)
  
(* term1 : P f x *)
(* term2 : f x *)
(* term should be of type bool *)
(* not really a conversion *)
fun bool_conv boolvar term subterm =
  if is_interesting_in term subterm
  then 
  (* term construction *)
    let val t1 = mk_eq (boolvar,subterm) in (* (b = f x) *)
    let val t2 = subst [subterm |-> boolvar] term in (* P b *)
    let val t3 = mk_forall (boolvar,mk_imp (t1,t2)) in
  (* first part  *)
    let val lemma1 = REFL subterm in
    let val th11 = ASSUME t3 in
    let val th12 = SPEC subterm th11 in
    let val th13 = UNDISCH th12 in
    let val th14 = PROVE_HYP lemma1 th13 in
    let val th15 = DISCH_ALL th14 in
  (* second part *)
    let val rwth1 = SYM (ASSUME t1) in
    let val th21 = ASSUME term in
    let val th22 = SUBS [rwth1] th21 in
    let val th23 = DISCH t1 th22 in
    let val th24  = GEN boolvar th23 in
    let val th25 = DISCH_ALL th24 in
    (* group together *)
      IMP_ANTISYM_RULE th25 th15
    end end end end end 
    end end end end end 
    end end end end end
  else raise UNCHANGED
 

fun bool_conv2 term = 
  let val subterm = find_term (is_interesting_in term) term in
    bool_conv ``b:bool`` term subterm
  end

fun rewrite_bool thm = rewrite bool_conv2 thm



(* recursively look into the subterms and apply bool_conv *)

val boolvar = ``c:bool``;
val subterm = ``!f:num -> bool . f x``;
val term = ``P (f x) (g !f:num -> bool . f x): bool``;
val thm = ASSUME term; 

bool_conv ``c:bool`` term subterm;
bool_conv2 term;
val thm = rewrite_bool thm;
val term = concl thm;
(* it matters if b is already used *)

 val t1 = mk_eq (boolvar,subterm); (* (b = f x) *)
 val t2 = subst [subterm |-> boolvar] term; (* P b *)
 val t3 = mk_forall (boolvar,mk_imp (t1,t2));
  (* first part  *)
 val lemma1 = REFL subterm;
 val th11 = ASSUME t3;
 val th12 = SPEC subterm th11;
 val th13 = UNDISCH th12;
 val th14 = PROVE_HYP lemma1 th13;
 val th15 = DISCH_ALL th14;
  (* second part *)
 val rwth1 = SYM (ASSUME t1);
 val th21 = ASSUME term; 
 val th22 = SUBS [rwth1] th21;
 val th23 = DISCH t1 th22;
 val th24  = GEN boolvar th23;
 val th25 = DISCH_ALL th24;



normalForms.CNF_CONV ``b:bool = c``;
show_assums := true;
DISCH ();


val thm11 = SUBS [thm10] thm5;

val goal = snd (top_goal ());


  STRIP_QUANT_CONV bool_conv ``!x. ?y. P (y:bool) (x:bool)``;
fun bool_conv_all term =
  let val (operator,argl) = strip_comb term in 
    case argl of
      [] => raise NORMALIZE_ERR "bool_conv" "empty list"
    | [arg] => if has_booltype arg 
               then 
                 if is_var_or_const arg
                 then REFL term
                 else bool_conv arg term
               else 
    | arg :: m =>
    
    
    
    
fun make_boolthml terml = map make_boolthm terml
    

fun extract_boolthm thm =
  let val term = concl thm in
  let val terml = find_terms (is_function) term in
  

fun rewrite_bool thm =  
  PURE_ONCE_REWRITE_RULE thml thm
  case terml of
    []
(* END BOOL REWRITE *)

(* NUM REWRITE *)
fun has_numty term = (type_of term = ``:num``)
(* easiest one *)
P (x:num) => P (x:num) /\ x >= 0


fun num_thm term = 
  let val axiom = arithmeticTheory.ZERO_LESS_EQ in
    SPEC term axiom
  end

fun free_in_rev a b = free_in b a;

fun is_interesting term subterm = 
  has_numty subterm andalso free_in subterm term 

(* term should be of type bool *)
(* don't go under a quantificator *) 
fun num_conv_fv term =
  let val terml = find_terms (is_interesting term) term in
  let val axioml = map num_thm terml in
  let val axiom = LIST_CONJ axioml in
  let val th2 = ASSUME term in
    CONJ axiom th2
  end end end end
 
(* add a test to test if the bv is present in the term *)
(* and test if the conv is already done *)

(* two things to do here *)
fun num_conv_forall term =
  (* term *)
  let val (qbvl,t) = strip_forall term in
  let val numbvl = filter has_numty qbvl in
  if numbvl = []
  then 
    raise UNCHANGED
  else
    let val thl = map num_thm numbvl in
    let val lemma1 = LIST_CONJ thl in
    let val termconj = concl (lemma1) in
  (* first part *)
    let val th11 = ASSUME term in
    let val th12 = SPEC_ALL th11 in
    let val th13 = ADD_ASSUM termconj th12 in
    let val th14 = DISCH termconj th13 in 
    let val th15 = GENL qbvl th14 in
    let val th16 = DISCH_ALL th15 in
  (* second part *)
    let val th21 = ASSUME (list_mk_forall (qbvl,mk_imp (termconj,t))) in
    let val th22 = SPEC_ALL th21 in
    let val th23 = UNDISCH th22 in
    let val th24 = PROVE_HYP lemma1 th23 in
    let val th25 = GENL qbvl th24 in
    let val th26 = DISCH_ALL th25 in
  (* regroup *)
      IMP_ANTISYM_RULE th16 th26
    end end end end end 
    end end end end end 
    end end end end end
    end end

show_assums := true ;

val term = ``!x.!y. x = 0``;
num_conv_forall term; 
 
 val (qbvl,t) = strip_forall term;
 val numbvl = filter has_numty qbvl;
 val thl = map num_thm numbvl;
 val lemma1 = LIST_CONJ thl;
 val termconj = concl (lemma1);
  (* first part *)
 val th11 = ASSUME term;
 val th12 = SPEC_ALL th11;
 val th13 = ADD_ASSUM termconj th12;
 val th14 = DISCH termconj th13; 
 val th15 = GENL qbvl th14;
  (* second part *)
 val th21 = ASSUME (list_mk_forall (qbvl,mk_imp (termconj,t)));
 val th22 = SPEC_ALL th21;
 val th23 = UNDISCH th22;
 val th24 = PROVE_HYP lemma1 th23;
 val th25 = GENL qbvl th24;
 val t
 
 
 
 !x P x |- !x P x
 !x P x |- P x 
 |- x >= 0 
 !x P x, x >= 0 |- P x 
 !x P x |- (x >= 0) => P x
 !x P x |- !x (x >= 0) => P x 
 (* other way *) 
 |- !x (x >= 0) => P x 
 |- (x >= 0) => P x 
 x >= 0 |- P x
 |- P x
 |- !x P x


 |- !x:num . P x <=> !x:num (x >= 0) => P x
  
  
  (*
  !x:num x >= 0 =>
  !x:num f x = 1 /\ f x > 0  
  *)  

  
 
fun num_conv_exists  
 
(* should also rewrite under the quantifier *) 
let rewrite_num term =

(*
num_conv ``P (x:num) (f (y:num)):bool`` 
DB.match ["arithmetic"] ``!n. 0 <= n``;
*)

fun rewrite_num term = 
  
(* END NUM REWRITE *)

(* FUN REWRITE *)   
fun fun_conv term = 

(*
First try ETA_CONV
*)
fun rewrite_fun thm =

 

       |- P (\x.t) <=> (!f. f x = t => P f)



(* END NUM REWRITE *)


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
  
  
  
  
  


