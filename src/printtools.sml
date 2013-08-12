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
val metisflag = ref (false,"metis-fail") (* check when it fails *)

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

(* counters for stats *)
val nb_problem = ref (0,"Problems    ")

val nb_m       = ref (0,"Polymorph   ") 
val nb_fun     = ref (0,"Lambda-lift ")
val nb_bool    = ref (0,"Bool Conv   ")
val nb_num     = ref (0,"Num Conv    ")
val nb_ho      = ref (0,"Higher Order")

val nb_unsat   = ref (0,"Unsat       ")
val nb_unknown = ref (0,"Unkown      ")
val nb_sat     = ref (0,"Sat         ")
val nb_timeout = ref (0,"Time Out    ")
val nb_parsing = ref (0,"Parsing Err ")
val nb_codeerr = ref (0,"Code Err    ")
val nb_beagerr = ref (0,"Beagle Err  ")
val nb_metis   = ref (0,"Metis fail  ")

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
  [nb_problem, nb_m, nb_fun, nb_bool, nb_num, nb_ho,
   nb_unsat, nb_unknown, nb_sat, 
   nb_timeout, nb_parsing, nb_codeerr, nb_beagerr, nb_metis];
 

(* test    
val str = "Higher Order: 102"
*) 
fun update_all_nb filename = 
  let val strl = readl filename in
    case strl of
      pb :: "\n" :: m :: f :: bool :: num :: ho :: "\n" :: 
      unsa :: unkn :: sat :: 
      time :: pars :: code :: beag :: meti :: fin
        =>
      (
      update_nb nb_problem (extract_nb pb);
      update_nb nb_m       (extract_nb m);
      update_nb nb_fun     (extract_nb f);
      update_nb nb_bool    (extract_nb bool);
      update_nb nb_num     (extract_nb num);
      update_nb nb_ho      (extract_nb ho);
      update_nb nb_unsat   (extract_nb unsa);
      update_nb nb_unknown (extract_nb unkn);
      update_nb nb_sat     (extract_nb sat);
      update_nb nb_timeout (extract_nb time);
      update_nb nb_parsing (extract_nb pars);
      update_nb nb_codeerr (extract_nb code);
      update_nb nb_beagerr (extract_nb beag);
      update_nb nb_metis   (extract_nb meti)
      )  
    | _ => reset_all_nb ()
  end
  handle _ => reset_all_nb ()  
  
end