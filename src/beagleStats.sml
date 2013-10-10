structure beagleStats :> beagleStats =
struct

open HolKernel Abbrev boolLib
     blibBtools blibDatatype 
  
fun STATS_ERR function message =
  HOL_ERR{origin_structure = "beagleStats",
	        origin_function = function,
          message = message}

(* flags *)
val mflag     = ref (false,"polymorph")
val fixpflag  = ref (false,"fixpoint")
val funflag   = ref (false,"lambda-lift")
val boolflag  = ref (false,"bool")
val numflag   = ref (false,"num")
val hoflag    = ref (false,"higher-order")
val metisflag = ref (false,"metis-fail") (* check when it fails *)
val proofflag = ref (false,"proof")
val allflag   = [mflag,fixpflag,funflag,boolflag,numflag,hoflag,
                 metisflag,proofflag]

fun flag_on flag = flag := (true,snd (!flag))
fun flag_off flag = flag := (false,snd (!flag))
fun flag_update flag value = flag := (value, snd(!flag))
fun flag_update_metis thml goal = 
  (
  flag_off metisflag;
  metisTools.METIS_TAC thml goal 
      handle _ => (flag_on metisflag; ([],fn x => (mk_thm goal)));
  ()
  )
fun reset_allflag () = app flag_off allflag
fun allflag_value () = map ! allflag


val nb_problem = ref (0,"Problems    ")

(* Code usage *)
val nb_m       = ref (0,"Polymorph   ") 
val nb_fixp    = ref (0,"Fixpoint    ")
val nb_fun     = ref (0,"Lambda-lift ")
val nb_bool    = ref (0,"Bool Conv   ")
val nb_num     = ref (0,"Num Conv    ")
val nb_ho      = ref (0,"Higher Order")
val nb_proof   = ref (0,"Proof       ")
val nb_metis   = ref (0,"Metis fail  ")
val nb_list1   = [nb_m,nb_fixp,nb_fun,nb_bool,nb_num,nb_ho,nb_proof,nb_metis]

(* Results *)
val nb_unsat   = ref (0,"Unsat       ")
val nb_unknown = ref (0,"Unkown      ")
val nb_sat     = ref (0,"Sat         ")
val nb_timeout = ref (0,"Time out    ")
val nb_parsing = ref (0,"Parsing err ")
val nb_codeerr = ref (0,"Code err    ")
val nb_beagerr = ref (0,"Beagle err  ")

val nb_list2   = [nb_unsat,nb_unknown,nb_sat,nb_timeout,nb_parsing,
                  nb_codeerr,nb_beagerr]

(* timerl *)
val timerl = mk_reflist 28 (0,"timerl      ")
                           
val metctime = ref 0;
val beactime = ref 0;
val tractime = ref 0;
val impctime = ref 0;

val faultl = [ref (0,"faultl      "),ref (0,"faultl      "),
              ref (0,"faultl      "),ref (0,"faultl      "),
              ref (0,"faultl      "),ref (0,"faultl      "),
              ref (0,"faultl      ")];


val nb_all = nb_problem :: (nb_list1 @ nb_list2 @ timerl @ faultl)

fun addone_nb nb = nb := ((fst (!nb)) + 1,snd (!nb))  

fun update_nb_flag nb flag = 
  if fst (!flag) then addone_nb nb else ()

fun update_nb nb n = nb := (n, snd (!nb))
 
fun update_nbl1 () =
  (
  update_nb_flag nb_m mflag;
  update_nb_flag nb_fixp fixpflag;
  update_nb_flag nb_fun funflag;
  update_nb_flag nb_bool boolflag;
  update_nb_flag nb_num numflag;
  update_nb_flag nb_ho hoflag;
  update_nb_flag nb_proof proofflag;
  update_nb_flag nb_metis metisflag
  )

fun update_nbl2 str =
  case str of
    "Unsatisfiable" => addone_nb nb_unsat
  | "Unknown" => addone_nb nb_unknown
  | "Satisfiable" => addone_nb nb_sat
  | "Time out" => addone_nb nb_timeout
  | "Parsing failed" => addone_nb nb_parsing
  | "Undefined" => addone_nb nb_codeerr
  | _ => addone_nb nb_beagerr
 

fun extract_nb str = 
  string_to_int (String.substring (str,14,(String.size str) - 15)) 

fun reset_nb nb = nb := (0,snd (!nb))  
fun reset_nbl nbl = app reset_nb nbl
fun reset_all_nb () = reset_nbl (nb_all)
 
fun update_nbl nbl strl =
  case (nbl,strl) of
    ([],_) => ()
  | (_,[]) => raise STATS_ERR "update_nbl" "not enough lines"
  | (nb :: m1,str :: m2) => (update_nb nb (extract_nb str); update_nbl m1 m2)
    
fun update_all_nb filename = 
  let val strl = readl filename in
    update_nbl nb_all strl
  end
  handle _ => reset_all_nb ()  
 
 
  
end