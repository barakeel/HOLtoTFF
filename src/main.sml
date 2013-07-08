structure main :> main =
struct
(* 
load "normalize"; open normalize; 
load "printtff"; open printtff;
*)


open HolKernel 
     normalize

(* Monomorphisation *)



(* Negate concl *)
fun negate_concl thm =
  let val t0 = concl thm in
  let val t1 = mk_neg t0 in
  let val th0 = ASSUME t1 in
  let val th1 = NOT_ELIM th0 in
    MP th1 thm
  end end end end   
 
(* input should have conclusion equal to false and goal be a negation *)
fun negate_concl_rev goal thm = CCONTR goal thm
(* need to memorise the goal somewhere to be able to replay the proof back *)
  
(* test 
show_assums :=  true ;
val thm = ASSUME ``A:bool``;
negate_concl thm;
*)

(* REWRITING and memorising dictionnaries *)
(* each term should be rewritten on its own ? *)
(* for now I just make a big conjunctions and rewrite it *)
(* for now thm should end with false *)
fun convert thm = 
  let val hypl = hyp thm in
  let val t0 = list_mk_conj hypl in
    (QCONV
    (
    beta_conv THENC
    eta_conv THENC
    normalForms.CNF_CONV THENC
    bool_conv THENC
    normalForms.CNF_CONV THENC
    fun_conv THENC
    app_conv THENC
    num_conv 
    ))
    t0 
  end end

val beagleproblemlocation =
  "/home/thibault/Desktop/Scalaproject/beagleproject/problem.p"
val testlocation = 
  "/home/thibault/Desktop/SMLproject/HOLtoTFF/output.txt"

(* should output a theorem but printtff should be rewritten *)
fun main thm = 
   let val th0 = negate_concl thm in
     let val eqth0 = convert th0 in
     let val term = rhs (concl eqth0) in (* this way you forgot to add app *)
     output_tff testlocation term 
   end end end 
   
   
(* test 
show_assums :=  true ;
val thm = mk_thm ([``x:bool``],``y:bool``);
main thm;


(* if you have an hypothesis in a conv it's not a problem *)
(*
A B C |- F
et
D |- B <=> (D => B')
 B' |- D => B'
A D => B' C D |-F
A B' C D |- F
*)

(* should make dictionnaries *)
(* free_var x_str *)
(* bound X_str *)
(* constant c_str *)
(* created bool b0 or B0*)
(* created fonction f0 or F0 *)
(* created app0 ... *)
(* skolem constant printed sk0_str *)
(* should create different names for every different constant created 
, reduce after if there's two of the same constant appearing with the same name *)
(* same definition  at the same level *) 



end