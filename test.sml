(* tools *)
open stringtools;
open listtools;
open mydatatype;
open extract_var;
open extracttype;
open namevar;
open nametype;
open higherorder;
open printtff;

(* problems *)
open boolproblem;
open numproblem;
open typetest;

(* TEST PROBLEM  *)

show_assums := true;
val thm = test_type1;
output_tff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;
(* END TEST PROBLEM *)

(* debug *)
    val goal = concl thm ;
    val hypl = hyp thm ; 
    val propl = hypl @ [concl thm] ;
  (* variable extraction *)
    val var_arity_cat = extract_varl propl ;
    val var_arity = erase3rdcomponent var_arity_cat ;
  (* type extraction *)
    val tyal = alltypel var_arity ;
    val leafvtyl = leafvtypel tyal ;
    val alphatyl = alphatypel tyal ; 
    val nodevtyl = nodevtypel tyal ;
  (* type name *)
    val alphaty_nm = addalphatypel alphatyl [] ;
    val leafvty_nm = addleafvtypel leafvtyl alphaty_nm ;
    val simp y_nm = addnodevsimp ypel nodevtyl leafvty_nm ;
    val tyadict = addnodevtypel nodevtyl simp y_nm ; 
  (* bound variable *)
    val bv_arity = get_bval var_arity_cat ; 
  (* free variable *)
    val fvcdc_arity_cat = erase_bv var_arity_cat ;
    val fvcdc_arity = erase3rdcomponent fvcdc_arity_cat ;
    val fvc_arity = get_fvcal var_arity_cat ; 
    val fvc_arity_nm = namefvcl fvc_arity ;
    val fvc_nm = erase2ndcomponent fvc_arity_nm ;
  (* axiom *)
    val axiomnm = nameaxioml hypl ;
  (* needed to call pr;tterm *)
    val state = (fvc_nm,[],tyadict) ;

(* end debug *)

(* TEST FUNCTIONS *)
open HolKernel;
is_minus ``5:int-6:int``;
pairSyntax

open folTools;
FOL_NORM ([mk_thm([],``!x. (!x. x = 0) /\ (x = 0) ``)]); (* rename bound variable *)
FOL_NORM ([ASSUME ``(\x.x) = (\z.w) ``]);
set_goal([],goal3);
e(FOL_NORM_TAC);
drop;
(* failure *)
FOL_NORM ([mk_thm([],``(\z.x) = (\y.y)``)]); (* mk_thm *)

open Hol_pp;
print_term goal;

open intSyntax;
type_of ``~1``;

open pairSyntax
strip_fun ``:(num->num) -> 'a ``;  
dest_type ``:num``;
numSyntax.int_of_term ``-521``;

open mlibTerm;
open mlibTptp;
read {filename = "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p"};
val formula = False;
write {filename = "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p"} formula;

(* betared *)

val term = `` ((\x.x) 0 = 0) /\ (\y.M y) x`` ;
val term = ``(\x.x) \x. f x ``;

(* Rewriting ... Normalizing *)
val term2 = rand (concl (REDEPTH_CONV BETA_CONV term));  (* to be rewritten *)
  (* may raise unchanged *)
val term3 = rand (concl (REDEPTH_CONV ETA_CONV term2)); (* may raise QConv.UNCHANGED *)
  (* skolemisation *) 
val term4 = rand (concl (REDEPTH_CONV SKOLEM_CONV term2));


(* END TEST FUNCTIONS *) 
