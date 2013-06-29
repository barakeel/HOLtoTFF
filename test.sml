(* tools *)
load "stringtools"; open stringtools;
load "listtools"; open listtools;
load "mydatataype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
load "namevar"; open namevar;
load "nametype"; open nametype;
load "higherorder"; open higherorder;
load "printtff"; open printtff;


(* TEST PROBLEM  *)
show_assums := true;
val term = ``x = 0``;
output_tff "/home/thibault/Desktop/SMLproject/HOLtoTFF/output.txt" term;
output_tff "/home/thibault/Desktop/Scalaproject/beagleproject/problem.p" term;
(* END TEST PROBLEM *)

(* need to standardize my code *)
(* test main function *)
val fval = collapse_lowestarity (get_fval (extract_var term)); 
val cal = collapse_lowestarity (get_cal (extract_var term));
  (* dict *)
val tyadict = create_tyadict term;write couple and record like this
val simpletyadict = get_simpletyadict tyadict;
val bvdict = create_bvdict term;
val fvdict = create_fvdict term;
val cdict = create_cdict term; 
(* end test main function *)
    
(* test print *)
let val file = TextIO.openOut path in 
let val pps = PP.mk_ppstream 
                {
                consumer  = fn s => TextIO.output (file,s),
                linewidth = 80,
                flush  = fn () => TextIO.flushOut file
                } 
in 
  (
  print_fvctyl pps fval fvdict tyadict;
  TextIO.closeOut file
  )  
end end

(* end test print *)  
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
