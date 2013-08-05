structure printresult :> printresult =
struct

open HolKernel Abbrev boolLib HOLPP 

fun ppres_thm pps thm = 
  (
  show_assums := true;
  add_string pps (thm_to_string thm);
  show_assums := false
  ) 
fun ppres_term pps term = add_string pps (term_to_string term)

fun ppres_thml pps thml = 
  case thml of
    [] => ()
  | thm :: m => (ppres_thm pps thm;
                 add_newline pps;
                 ppres_thml pps m)

fun ppres_terml pps terml =
  case terml of
    [] => ()
  | [term] => ppres_term pps term
  | term :: m => (ppres_term pps term;
                  add_string pps ",";
                  ppres_terml pps m)

fun ppres_goal pps goal =
  (
  add_string pps "["; ppres_terml pps (fst goal); add_string pps "]";
  add_string pps " ?- ";
  ppres_term pps (snd goal)
  )     
    
fun ppres_problem pps thml goal =
  (
  begin_block pps CONSISTENT 0;
    add_string pps "User theorems: "; 
    ppres_thml pps thml; add_newline pps; 
    add_string pps "Goal: "; 
    ppres_goal pps goal; add_newline pps;
  end_block pps
  )
 
fun output_tffgoalpath addresspath filepath =
  let val file = TextIO.openOut addresspath in 
    (
    TextIO.output (file,filepath); 
    TextIO.closeOut file
    )  
  end 

fun output_result path goal SZSstatus mflag =  
  let val file = TextIO.openAppend path in 
  let val thm = mk_thm goal in
    (
    TextIO.output (file,SZSstatus ^ ": "); 
    if mflag then TextIO.output (file,"(polymorph) ") else ();
    show_assums := true;
    TextIO.output (file,(thm_to_string thm) ^ "\n"); 
    show_assums := false;
    TextIO.closeOut file
    )  
  end end
  
  
end