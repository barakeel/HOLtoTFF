structure printtools :> printtools =
struct

open HolKernel Abbrev boolLib numSyntax HOLPP
     stringtools listtools mydatatype
     
fun PRINTTOOLS_ERR function message =
    HOL_ERR{origin_structure = "tools",
	    origin_function = function,
            message = message}

(* flags *)
val mflag = ref (false,"polymorph")
val funflag = ref (false,"lambda-lift")
val boolflag = ref (false,"bool")
val numflag = ref (false,"num")
val hoflag = ref (false,"higher-order")
val predflag = ref (false,"predicate")
val metisflag = ref (false,"metis-fail") (* check when it fails *)
val proofflag = ref (false,"proof")
val allflag = [mflag,funflag,boolflag,numflag,hoflag,predflag,
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

(* counters for stats *)
val nb_problem = ref (0,"Problems    ")

val nb_m       = ref (0,"Polymorph   ") 
val nb_fun     = ref (0,"Lambda-lift ")
val nb_bool    = ref (0,"Bool Conv   ")
val nb_num     = ref (0,"Num Conv    ")
val nb_ho      = ref (0,"Higher Order")
val nb_pred    = ref (0,"Predicate   ")

val nb_unsat   = ref (0,"Unsat       ")
val nb_unknown = ref (0,"Unkown      ")
val nb_sat     = ref (0,"Sat         ")
val nb_timeout = ref (0,"Time Out    ")
val nb_parsing = ref (0,"Parsing Err ")
val nb_codeerr = ref (0,"Code Err    ")
val nb_beagerr = ref (0,"Beagle Err  ")
val nb_metis   = ref (0,"Metis fail  ")
val nb_proof   = ref (0,"Proof       ")

fun addone_nb nb = nb := ((fst (!nb)) + 1,snd (!nb))  

fun update_nb_flag nb flag = 
  if fst (!flag) then addone_nb nb else ()

fun update_nb nb n = nb := (n, snd (!nb))
  
fun readl filename = 
  let
    val file = TextIO.openIn filename
    fun loop file =
      case TextIO.inputLine file of
        SOME line => line :: loop file
      | NONE      => []
  in
    loop file before TextIO.closeIn file
  end
  
fun string_to_int_aux l =
  case l of
    [] => 0
  | c :: m => case Char.toString c of 
                "0" => 0 + 10 * (string_to_int_aux m)
              | "1" => 1 + 10 * (string_to_int_aux m)
              | "2" => 2 + 10 * (string_to_int_aux m)
              | "3" => 3 + 10 * (string_to_int_aux m)
              | "4" => 4 + 10 * (string_to_int_aux m)
              | "5" => 5 + 10 * (string_to_int_aux m)
              | "6" => 6 + 10 * (string_to_int_aux m)
              | "7" => 7 + 10 * (string_to_int_aux m)
              | "8" => 8 + 10 * (string_to_int_aux m)
              | "9" => 9 + 10 * (string_to_int_aux m)
              | _   => raise PRINTTOOLS_ERR "string_to_int" "not a number"
                         
fun string_to_int str = string_to_int_aux (rev (String.explode str))

fun extract_nb str = 
  string_to_int (String.substring (str,14,(String.size str) - 15)) 

fun reset_nb nb = nb := (0,snd (!nb))  
fun reset_nbl nbl = app reset_nb nbl
fun reset_all_nb () = reset_nbl 
  [nb_problem, nb_m, nb_fun, nb_bool, nb_num, nb_ho, nb_pred, 
   nb_proof, nb_metis,
   nb_unsat, nb_unknown, nb_sat, 
   nb_timeout, nb_parsing, nb_codeerr, nb_beagerr];
 

(* test    
val str = "Higher Order: 102"
*) 
fun update_nbl nbl strl =
  case (nbl,strl) of
    ([],_) => ()
  | (_,[]) => ()
  | (nb :: m1,str :: m2) => (update_nb nb (extract_nb str); update_nbl m1 m2)
    
fun update_all_nb filename = 
  let val strl = readl filename in
    case strl of
      pb :: "\n" ::
      m :: f :: bool :: num :: ho :: pred :: proof :: meti :: "\n" :: 
      unsa :: unkn :: sat :: time :: pars :: code :: beag :: fin
        =>
      (
      update_nbl
        [nb_problem,nb_m,nb_fun,nb_bool,nb_num,nb_ho,nb_pred,nb_proof,nb_metis,
         nb_unsat,nb_unknown,nb_sat,nb_timeout,nb_parsing,nb_codeerr,nb_beagerr]
        [pb,m,f,bool,num,ho,pred,proof,meti,
         unsa,unkn,sat,time,pars,code,beag]
      )  
    | _ => reset_all_nb ()
  end
  handle _ => reset_all_nb ()  
  
end