structure printresult :> printresult =
struct

open HolKernel Abbrev boolLib HOLPP Hol_pp

type goal = (Term.term list * Term.term) 

fun pp_thm pps thm = add_string pps (thm_to_string thm)
fun pp_term pps term = add_string pps (term_to_string term)

fun pp_thml pps thml = 
  case thml of
    [] => ()
  | thm :: m => (pp_thm pps thm;
                 add_newline pps;
                 pp_thml pps m)

fun pp_terml pps terml =
  case terml of
    [] => ()
  | term :: m => (pp_term pps term;
                  add_newline pps;
                  pp_terml pps m)

fun pp_goal pps goal =
  (
  add_string pps "  (* hypothesis list *) "; add_newline pps; 
  pp_terml pps (fst goal); 
  add_string pps "  (* concl *)"; add_newline pps; 
  pp_term pps (snd goal); add_newline pps
  )     
    
fun print_result pps thml goal eqthm prepareflag =
  (
  begin_block pps CONSISTENT 0;
  add_string pps "(* User provided theorem *)"; add_newline pps; 
    pp_thml pps thml;
    add_newline pps; 
  add_string pps "(* Goal *)"; add_newline pps; 
    pp_goal pps goal;
    add_newline pps;
  if prepareflag 
  then
    (add_string pps "(* Conversion theorem *)"; add_newline pps;
     show_assums :=  true;
     pp_thm pps eqthm;
     show_assums := false;
     add_newline pps)
  else ();
  end_block pps
  ) 

fun output_result path thml goal eqthm prepareflag =
  let val file = TextIO.openOut path in 
  let val pps = PP.mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 80,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in 
    (
    print_result pps thml goal eqthm prepareflag; 
    TextIO.closeOut file
    )  
  end end

fun output_tffpath filepath =
  let val file = TextIO.openOut "filepath.txt" in 
    (
    TextIO.output (file, filepath); 
    TextIO.flushOut file;
    TextIO.closeOut file
    )  
  end 


  
end