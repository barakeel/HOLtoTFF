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
fun rewrite_cnf thm =
  let val eqthm = QCONV CNF_CONV prop in
    SUBS [eqthm] thm 
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


fun rewrite_app1 thm =
(* if some function appears with different arguments then *)  
(* bounded function appears with lowest_arity equal to 0 *)
(* Same definition as let *)

(* input: a comb term *) 
(* app should supports multiple arguments *)
fun (make_appassume:conv) term =
  let val (operator,argl) = strip_comb term in
  let val arity = length argl in
  let val ty = mk_type ("fun", [type_of operator,type_of operator]) in
  let val app = mk_var ("app_" ^ (Int.toString arity), ty) in    
  let val appdeflhs =  mk_abs (operator, mk_abs (hd argl, term)) in
  let val appdef = mk_eq (app, appdeflhs) in  
  let val assume = ASSUME appdef in
    assume
  end end end end end end end
 
 
(* 
app_1 = \f x. f x |- app_1 = \f x. f x
app_1 = \f x. f x |- app_1 f x = (\f x. f x) f x 
app_1 = \f x. f x |- app_1 f x = f x 
*)
(* need to beta_conv or cnf_conv the result *)
fun make_appthm term =
  let val assume = make_appassume term in
  let val (operator,arg) = dest_comb term in
     AP_THM (AP_THM assume operator) arg
  end end
  
make_appthm ``f x``;

  is_var f
  term, mk_var ("b", ``:bool``))) 
 f x = A_1 f x
(* APP *)
(* doesn't create boolean arguments *)
(* doesn't add new type *)


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
  
  
  
  
  
  
  


