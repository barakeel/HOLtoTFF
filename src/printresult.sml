structure printresult :> printresult =
struct

open HolKernel Abbrev boolLib HOLPP 
     tools conv printtools

(* Path (absolute) *)
val directory = "/home/thibault/Desktop/SMLproject/HOLtoTFF/"
fun mk_holpath filename = directory ^ filename ^ "_hol"  
fun mk_tffpath filename =  directory ^ filename ^ "_tff" 
fun mk_SZSstatuspath filename = directory ^ filename ^ "_tff_SZSstatus"
fun mk_resultpath filename = directory ^ filename ^ "_result"
fun mk_convpath filename = directory ^ filename ^ "_conv"
fun mk_addresspath () = directory ^ "filepath.txt"
fun mk_tffsavepath filename = directory ^ filename ^ "_tffsave"
fun mk_proofpath filename = directory ^ filename ^ "_proof"

fun output_tffgoalpath filepath =
  let val file = TextIO.openOut (mk_addresspath()) in 
    (
    TextIO.output (file,filepath); 
    TextIO.closeOut file
    )  
  end 
 
fun output_thml file thml = 
  case thml of
    [] => ()
  | thm :: m => 
    (TextIO.output (file,(thm_to_string thm) ^ "\n"); 
     output_thml file m)

fun outstream_flagl_aux file flagl =
  case flagl of
    [] => ()
  | (value,name) :: m => 
    if value 
    then (TextIO.output (file, name ^ " "); outstream_flagl_aux file m)
    else outstream_flagl_aux file m
    
fun outstream_flagl file flagl =
  (   
  if exists fst flagl then TextIO.output (file,"Info: ") else ();
  outstream_flagl_aux file flagl;
  if exists fst flagl then TextIO.output (file,"\n") else ()
  )

fun output_result filename thml goal SZSstatus flagl =  
  let val file = TextIO.openAppend (mk_resultpath filename) in 
  let val thm = mk_thm goal in
    (
    TextIO.output (file,"Status: " ^ SZSstatus ^ "\n");
    outstream_flagl file flagl;
    show_assums := true;
    TextIO.output (file,"Thm list: " ^ "\n"); 
    output_thml file thml;
    TextIO.output (file,"Goal: " ^ "\n");
    TextIO.output (file,(thm_to_string thm) ^ "\n\n\n"); 
    show_assums := false;
    TextIO.closeOut file
    )  
  end end
  
fun outstream_eqth_info file str eqth =
  if lhs (concl eqth) = rhs (concl eqth) then ()
  else TextIO.output (file,str)

fun output_beagle_conv filename goal =
  let val eqth1 = QCONV normalForms.CNF_CONV (only_hypg goal) in 
  let val eqth2 = QCONV fun_conv  (rhs (concl eqth1)) in 
  let val eqth3 = QCONV bool_conv (rhs (concl eqth2)) in 
  let val eqth4 = QCONV num_conv  (rhs (concl eqth3)) in 
  let val eqth5 = QCONV normalForms.CNF_CONV (rhs (concl eqth4)) in 
    (
      let val file = TextIO.openAppend (mk_convpath filename) in
        (  
        outstream_eqth file "CNF1" eqth1;
        outstream_eqth file "FUN " eqth2;
        outstream_eqth file "BOOL" eqth3;
        outstream_eqth file "NUM " eqth4;
        outstream_eqth file "CNF2" eqth5;
        TextIO.output(file,"\n");
        TextIO.closeOut file 
        )
      end
    ;
      let val file = TextIO.openAppend (mk_resultpath filename) in
        (  
        TextIO.output(file,"Conv_info: ");
        outstream_eqth_info file "CNF1 " eqth1;
        outstream_eqth_info file "FUN " eqth2;
        outstream_eqth_info file "BOOL " eqth3;
        outstream_eqth_info file "NUM " eqth4;
        outstream_eqth_info file "CNF2 " eqth5;
        TextIO.output(file,"\n");
        TextIO.closeOut file 
        )
      end
    )
end end end end end  
  
  
end