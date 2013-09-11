structure beaglePrintresult :> beaglePrintresult =
struct

open HolKernel Abbrev boolLib
     blibBtools blibSyntax
     beagleStats

(* Path (absolute) *)
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"

fun mk_proofpath filename = directory ^ filename ^ "_tff_proof"
fun mk_addresspath () = directory ^ "filepath.txt"
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_resultpath filename = directory ^ filename ^ "_result"
fun mk_convpath filename = directory ^ filename ^ "_conv"
fun mk_errpath filename = directory ^ filename ^ "_error"
fun mk_tfferrpath filename = directory ^ filename ^ "_tff_error"
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

fun output_problem file thml goal =
  (
  TextIO.output (file,"Thm list: " ^ "\n"); 
  output_thml file thml;
  TextIO.output (file,"Goal: ");
  TextIO.output (file,(goal_to_string goal) ^ "\n")
  )
  
fun write_result filename thml goal n SZSstatus flagl =  
  let val file = TextIO.openAppend filename in 
    (
    TextIO.output (file,"Number: " ^ Int.toString (fst n) ^ "\n");
    TextIO.output (file,"Status: " ^ SZSstatus ^ "\n");
    output_flagl file flagl;
    output_problem file thml goal;
    TextIO.output (file,"\n");
    TextIO.closeOut file
    )  
  end
 
(* write error *)
fun write_err filename s f m =
  let val file = TextIO.openAppend filename in 
    (
    TextIO.output (file,"structure: " ^ s ^ 
                        " function: " ^ f ^ 
                        " message: " ^ m ^ "\n");
    TextIO.closeOut file
    )  
  end
  
  
end