structure printresult :> printresult =
struct

open HolKernel Abbrev boolLib
     tools conv tactic 
     printtools

(* Path (absolute) *)
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"

fun mk_SZSstatuspath filename = directory ^ filename ^ "_tff_SZSstatus"
fun mk_addresspath () = directory ^ "filepath.txt"
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_resultpath filename = directory ^ filename ^ "_result"
fun mk_convpath filename = directory ^ filename ^ "_conv"
fun mk_errpath filename = directory ^ filename ^ "_error"
fun mk_tfferrpath filename = directory ^ filename ^ "_tfferror"
fun mk_statspath filename = directory ^ filename ^ "_stats"

(* stats *)
fun output_nb file nb =
  TextIO.output (file,(snd nb) ^ ": " ^ (Int.toString(fst nb)) ^ "\n");

fun output_nbl file nbl = app (output_nb file) nbl

fun write_stats filename nb_pb nbl1 nbl2 =
  let val file = TextIO.openOut (mk_statspath filename) in
    (  
    output_nb file nb_pb;
    TextIO.output (file,"\n");
    output_nbl file nbl1;
    TextIO.output (file,"\n");
    output_nbl file nbl2;
    TextIO.output (file,"\n");
    TextIO.closeOut file 
    )
  end

(* write a path to the tff file *)
fun write_tffpath tffpath =
  let val file = TextIO.openOut (mk_addresspath()) in 
    (
    TextIO.output (file,tffpath); 
    TextIO.closeOut file
    )  
  end 
 
(* write results *) 
fun output_thml file thml = 
  case thml of
    [] => ()
  | thm :: m => 
    (TextIO.output (file,(thm_to_string thm) ^ "\n"); 
     output_thml file m)

fun output_flagl_aux file flagl =
  case flagl of
    [] => ()
  | (value,name) :: m => 
    if value 
    then (TextIO.output (file, name ^ " "); output_flagl_aux file m)
    else output_flagl_aux file m
    
fun output_flagl file flagl =
  (   
  if exists fst flagl then TextIO.output (file,"Info: ") else ();
  output_flagl_aux file flagl;
  if exists fst flagl then TextIO.output (file,"\n") else ()
  )

fun output_METIS_TAC file thml goal =
  let val success = ref true in
    (
    
    if (!success) 
    then TextIO.output (file,"success\n")
    else TextIO.output (file,"failure\n")
    )
  end

fun output_problem file thml goal =
  (
  TextIO.output (file,"Thm list: " ^ "\n"); 
  output_thml file thml;
  TextIO.output (file,"Goal: ");
  TextIO.output (file,(goal_to_string goal) ^ "\n")
  )
  
fun write_result filename thml goal SZSstatus flagl =  
  let val file = TextIO.openAppend filename in 
    (
    TextIO.output (file,"Status: " ^ SZSstatus ^ "\n");
    output_flagl file flagl;
    output_problem file thml goal;
    TextIO.output (file,"\n");
    TextIO.closeOut file
    )  
  end 
  
(* write conversion *)  
fun output_eqth file str eqth =
  if lhs (concl eqth) = rhs (concl eqth) then ()
  else (
       TextIO.output (file,str ^ ": ");
       TextIO.output (file,(term_to_string (rhs (concl eqth))) ^ "\n")
       )

fun is_refl eqth = (rhs (concl eqth) = lhs (concl eqth))

fun flags_update_conv thml goal =
  let val goal1 = hd (fst (PROBLEM_TO_GOAL_TAC thml goal)) in
  let val eqth1 = QCONV normalForms.CNF_CONV (only_hypg goal1) in 
  let val eqth2 = QCONV fun_conv  (rhs (concl eqth1)) in 
  let val eqth3 = QCONV bool_conv (rhs (concl eqth2)) in 
  let val eqth4 = QCONV num_conv  (rhs (concl eqth3)) in 
    (
    flag_update funflag (not (is_refl eqth2));
    flag_update boolflag (not (is_refl eqth3));
    flag_update numflag (not (is_refl eqth4))
    ) 
  end end end end end

fun write_conv filename thml goal =
  let val goal1 = hd (fst (PROBLEM_TO_GOAL_TAC thml goal)) in
  let val eqth1 = QCONV normalForms.CNF_CONV (only_hypg goal1) in 
  let val eqth2 = QCONV fun_conv  (rhs (concl eqth1)) in 
  let val eqth3 = QCONV bool_conv (rhs (concl eqth2)) in 
  let val eqth4 = QCONV num_conv  (rhs (concl eqth3)) in 
  let val eqth5 = QCONV normalForms.CNF_CONV (rhs (concl eqth4)) in 
    let val file = TextIO.openAppend (mk_convpath filename) in
      (  
      output_eqth file "CNF1" eqth1;
      output_eqth file "FUN " eqth2;
      output_eqth file "BOOL" eqth3;
      output_eqth file "NUM " eqth4;
      output_eqth file "CNF2" eqth5;
      TextIO.output(file,"\n");
      TextIO.closeOut file 
      )
    end
end end end end end end 

(* write error *)
fun write_err filename thml goal f m =
  let val file = TextIO.openAppend (mk_resultpath filename) in 
    (
    TextIO.output (file,"function: " ^ f ^ " message: " ^ m);
    output_problem file thml goal;
    TextIO.closeOut file
    )  
  end
  
  
end