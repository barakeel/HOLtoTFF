(* tools *)
open stringtools;
open listtools;
open mydatatype;
open extractvar;
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
outputtff "/home/thibault/Desktop/eclipsefile/beagleproject/problem.p" thm;
(* END TEST PROBLEM *)

(* debug *)
    val goal = concl thm ;
    val hypl = hyp thm ; 
    val propl = hypl @ [concl thm] ;
  (* variable extraction *)
    val var_narg_cat = extractvarl propl ;
    val var_narg = erase3rdcomponent var_narg_cat ;
  (* type extraction *)
    val ty_narg = alltypel var_narg ;
    val leafvtyl = leafvtypel ty_narg ;
    val alphatyl = alphatypel ty_narg ; 
    val nodevtyl = nodevtypel ty_narg ;
  (* type name *)
    val alphaty_nm = addalphatypel alphatyl [] ;
    val leafvty_nm = addleafvtypel leafvtyl alphaty_nm ;
    val simp y_nm = addnodevsimp ypel nodevtyl leafvty_nm ;
    val tydict = addnodevtypel nodevtyl simp y_nm ; 
  (* bound variable *)
    val bv_narg = get_bval var_narg_cat ; 
  (* free variable *)
    val fvcdc_narg_cat = erase_bv var_narg_cat ;
    val fvcdc_narg = erase3rdcomponent fvcdc_narg_cat ;
    val fvc_narg = get_fvcal var_narg_cat ; 
    val fvc_narg_nm = namefvcl fvc_narg ;
    val fvc_nm = erase2ndcomponent fvc_narg_nm ;
  (* axiom *)
    val axiomnm = nameaxioml hypl ;
  (* needed to call pr;tterm *)
    val state = (fvc_nm,[],tydict) ;

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
