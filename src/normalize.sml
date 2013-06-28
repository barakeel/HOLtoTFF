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
fun rewrite_cnf thm =
  let val eqthm = QCONV CNF_CONV prop in
    EQ_MP eqthm thm 
  end 


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
(* bound is only a variable not a term *)
(* this problem will be solved at the end *)
(* it's in normal form *)
fun has_booltype term = (type_of term = ``:bool``)
(* input : a list of combination *)
(* output : a thml *)


(* output: thm*)
fun is_var_or_const term = is_var term or else is_const term

(* input: term is a comb *)
(* output: theorem list *)
(* f = g can be rewrite !x f x = g x *) FUN_CONV

(* boolarg should be of type bool *)
(* choose a new name for a free vars *)


fun (bool_conv: conv) term  =
  if has_booltype term 
  then ASSUME (mk_eq (term, mk_var ("b", ``:bool``))) 
  else REFL term

STRIP_QUANT_CONV (STRIP_QUANT_CONV  bool_conv) ``!x. ?y. P (y:bool) (x:bool)``
  

val thm = COMB_CONV bool_conv ``f (A /\ B)``;
show_assums := true;
DISCH ();

  
fun bool_conv term =
  let val (operator,argl) = strip_comb term in 
    case argl of
      [] => raise NORMALIZE_ERR "bool_conv" "empty list"
    | [arg] => if has_booltype arg 
               then 
                 if is_var_or_const arg
                 then QCONV ALL_CONV term
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
  

fun has_numtype term = (type_of term = ``:num``)

fun rewrite_num thm = 
  let val term = concl thm in
  let val terml = find_terms (has_numtype) term in
  


fun rewrite_fun thm =
(*
First 
  try ETA_CONV
Then 
  for every free function make this rewriting thm
  f x = t |- \x. t = f 
*) 



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



(* APP *)
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
  
  
  
  
  


