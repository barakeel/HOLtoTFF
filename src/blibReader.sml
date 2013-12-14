structure blibReader :> blibReader =
struct

open HolKernel Abbrev boolLib numSyntax
     blibDatatype blibBtools blibBrule blibBtactic
     blibSyntax blibTffsyntax blibFreshvar blibExtractvar
     
     
fun READER_ERR function message =
  HOL_ERR{origin_structure = "blibReader",
          origin_function = function,
          message = message}
 
(* global reference *)
val rbcdict: (string * term) list ref = ref []
val defl: (term list) ref = ref []

(* TOOLS *)
fun split_char ch str =  
  if char_in ch str  
  then
    let val p = char_place ch str in
      first_n_char p str :: 
      split_char ch (rm_first_n_char (p+1) str)  
    end
  else [str]

fun number_par_aux charl n place =
  case charl of
    [] => []
  | c :: m => case Char.toString c of
                "(" => (("(",n + 1),place) :: number_par_aux m (n + 1) (place + 1)
              | ")" => ((")",n),place) :: number_par_aux m (n - 1) (place + 1)
              | str => ((str,n),place) :: number_par_aux m n (place + 1)

fun number_par str = number_par_aux (String.explode str) 0 0
 
fun split_outerchar ch str = 
  let val l = number_par str in
    if is_member (ch,0) (map fst l) 
    then
      let val p = lookup (ch,0) l in
        first_n_char p str :: 
        split_outerchar ch (rm_first_n_char (p+1) str)  
      end
    else [str]
  end

(* test 
val str = "0,$sum(Xx1,Xx2)";
split_outerchar "," str;
*)

fun is_closebefore str =
  is_member (")",1) (tl (rev (map fst (number_par str)))) 

fun erase_outerpar str =
  if first_n_char 1 str = "(" andalso last_n_char 1 str = ")" andalso
  not (is_closebefore str)
  then String.substring (str,1,String.size str - 2)
  else str

fun erase_spaces str =
  if str = "" then ""
  else 
    if first_n_char 1 str = " "
    then erase_spaces (rm_first_n_char 1 str)
    else (first_n_char 1 str) ^ (erase_spaces (rm_first_n_char 1 str))
  
(* test
readl "beagletacresult/beagletac_tff_proof";
get_tffaxioml "beagletacresult/beagletac_tff_proof";
*) 
 
(* test
val lit = "fx(x,g(y))"; 
val str = " bon j o ur ";
*) 
 
(* READ CLAUSES *)
fun get_tffoperator tffterm = 
  let val p = char_place "(" tffterm in
    first_n_char p tffterm
  end

fun get_tffargl tffterm =
  let val p = char_place "(" tffterm in
     split_outerchar "," (erase_outerpar (rm_first_n_char p tffterm))
  end

fun is_beaglec tffvar = 
  (first_n_char 1 tffvar = "#") andalso 
  is_lowerword (rm_first_n_char 1 tffvar)
    
fun read_var tffvar rvdict = 
  if is_member tffvar (map fst rvdict) 
    then lookup tffvar rvdict
  else if success Arbnum.fromString tffvar
    then intSyntax.mk_injected (mk_numeral (Arbnum.fromString tffvar))
  else if is_tfffunctor tffvar 
    then read_tfffunctor tffvar
  else if is_tffbool tffvar 
    then read_tffbool tffvar
  else if is_beaglec tffvar
    then if is_member tffvar (map fst (!rbcdict)) 
         then lookup tffvar (!rbcdict)
         else 
           (
           let val v = mk_var (tffvar,``:int``) in
           let val newv = mk_newvar v ((map snd (!rbcdict)) @ (map snd rvdict)) in
             rbcdict := add_entry (tffvar,newv) (!rbcdict)
           end end
           ;
           lookup tffvar (!rbcdict)
           )
  else raise READER_ERR "read_var" tffvar

fun is_tffvar tffterm rvdict = 
  is_member tffterm (map fst rvdict)  orelse 
  success Arbnum.fromString tffterm orelse
  is_tfffunctor tffterm orelse
  is_tffbool tffterm orelse
  is_beaglec tffterm

fun read_tffterm tffterm rvdict =
  if is_tffvar tffterm rvdict
  then read_var tffterm rvdict
  else 
    let val oper = read_var (get_tffoperator tffterm) rvdict in 
    let val tffargl = get_tffargl tffterm in
      list_mk_comb (oper,map (inv read_tffterm rvdict) tffargl)
    end end

fun read_tfflit tfflit rvdict =
  let val lit = erase_outerpar tfflit in
    if char_in "~" lit
    then mk_neg (read_tfflit (rm_first_n_char 1 lit) rvdict)
    else 
      if not (char_in "=" lit) then read_tffterm lit rvdict
      else if not (char_in "!" lit) then
        let val p = char_place "=" lit in
        let val t2 = first_n_char p lit in
        let val t1 = rm_first_n_char (p+1) lit in 
          mk_eq (read_tffterm t1 rvdict,read_tffterm t2 rvdict)
          handle _ => raise READER_ERR "read_tfflit" (t1 ^ ", " ^ t2)
        end end end
      else
        let val p = char_place "!" lit in
        let val t1 = first_n_char p lit in
        let val t2 = rm_first_n_char (p+2) lit in 
          mk_neg (mk_eq (read_tffterm t1 rvdict,read_tffterm t2 rvdict))
          handle _ => raise READER_ERR "read_tfflit" (t1 ^ ", " ^ t2)
        end end end
  end

(* test
val rvdict = [("Xx1",``Xx1:num``)];
val tffterm = "$lesseq(0,$sum(Xx1,Xx2))";
val tfflit = "~$lesseq(0,Xx1)";
read_tfflit tfflit rvdict;
val tffterm = "0";
val tffterm = "Xx1";
*)

fun read_tffdisj tffdisj rvdict =
  let val disj = erase_outerpar tffdisj in
    if not (char_in "|" disj) then read_tfflit disj rvdict
    else
      let val litl = split_char "|" disj in
        list_mk_disj (map (inv read_tfflit rvdict) litl)
      end 
  end

(* test
val tffdisj =  
  "(~$lesseq(0,Xx2)|~$lesseq(0,Xx1)|$lesseq(0,$sum(Xx1,Xx2)))";
val rvdict = [("Xx1",``Xx1:num``)];
read_tffdisj tffdisj rvdict;
*)

(* DICTIONNARIES *)
(* tools *)
fun mk_rtydict tyadict =
  case tyadict of
    [] => []  
  | ((ty,arity),nm) :: m => (nm,ty) :: mk_rtydict m

fun rev_dict rdict =
  case rdict of
    [] => []
  | (a,nm) :: m => (nm,a) :: rev_dict m

 
(* create free variables dictionnary *) 
fun mk_rvdict fvdict cdict = 
  rev_dict cdict @ rev_dict fvdict

fun mk_rdict (dict:((hol_type * int) * string) list *
                   (term * string) list *
                   (term * string) list *
                   (term * string) list )
   = (mk_rtydict (#1 dict), mk_rvdict (#3 dict) (#4 dict))

(* create bound variables dictionnary *)
fun prep_tffbvl clause =
  let val p1 = char_place "[" clause in
  let val p2 = char_place "]" clause in
    split_char "," (String.substring (clause,p1 + 1,p2 - p1 - 1))
  end end
 
fun mk_rbvl tffbvlcpl (rtydict,rvdict) = 
  case tffbvlcpl of
    [] => []
  | [str1,str2] :: m => mk_var (str1,lookup str2 rtydict) :: 
                        mk_rbvl m (rtydict,rvdict)
  | _ => raise READER_ERR "mk_rbvl" ""
    
fun mk_freshrbvl tffbvlcpl (rtydict,rvdict) =
  let val rbvl = mk_rbvl tffbvlcpl (rtydict,rvdict) in
    mk_newvarl rbvl (map snd rvdict)
  end
 
fun mk_rbvdict_aux tffbvlcpl freshrbvl =
  if not (length tffbvlcpl = length freshrbvl) 
  then raise READER_ERR "mk_rbvdict_aux" ""
  else
    case tffbvlcpl of
      [] => []
    | [str1,str2] :: m => (str1,hd freshrbvl) :: mk_rbvdict_aux m (tl freshrbvl)
    | _ => raise READER_ERR "mk_rbvdict_aux" ""

fun mk_rbvdict clause (rtydict,rvdict) =
  let val tffbvl = prep_tffbvl clause in
  let val tffbvlcpl = map (split_char ":") tffbvl in
  let val freshrbvl = mk_freshrbvl tffbvlcpl (rtydict,rvdict) in
    mk_rbvdict_aux tffbvlcpl freshrbvl
  end end end
(* END DICTIONNARY *)

fun get_tffdisj clause = 
  let val p = char_place "]" clause in
    String.substring (clause, p + 2, String.size clause - p - 2)
  end  
    
(* #1 rdict = rtydict *)
(* #2 rdict = rvdict *)

fun read_tffclause tffclause (rtydict,rvdict) =
  let val clause = erase_spaces (erase_outerpar tffclause) in
    if not (char_in "[" clause) then read_tffdisj clause rvdict
    else
      let val tffdisj = get_tffdisj clause in
      let val rbvdict = mk_rbvdict clause (rtydict,rvdict) in
      let val bvl = map snd rbvdict in
        list_mk_forall (bvl,read_tffdisj tffdisj (rbvdict @ rvdict))
      end end end
  end

(* test
val tfflit = "(f(x,y))";
val tffdisj = "(f(x,y)=f(a,b))|~(y=x)";
val tffclause = "![x:$int,y:$int]:((f(x,y)=f(a,b))|~(y=x))";
val tffclause = "(![Xx2: $int, Xx1: $int]: (~$lesseq(0, Xx2)" ^
                " | ~$lesseq(0, Xx1) | $lesseq(0, $sum(Xx1, Xx2))))";

val tffclause = "~($sum(xx,2)=xz)";
val rvdict = [("f",mk_var ("f",``:num -> num -> bool``))];
val rtydict = [("$int",``:num``)];
read_tffclause tffclause (rtydict,rvdict);
*)

(* READ FILE *)
fun is_intro line = 
  if success (first_n_char 4) line
  then first_n_char 4 line = "tff("
  else false
  
fun get_intro_aux line =
  let val p1 = char_place "," line in
  let val p2 = char_place "," (rm_first_n_char (p1 + 1) line) in
    String.substring (line,p1 + 1, p2)
  end end

fun get_intro line =
  if success get_intro_aux line 
  then get_intro_aux line 
  else "NOINFO"

fun get_tffclause line = 
  if success String.substring (line,4,String.size line - 6)
  then String.substring (line,4,String.size line - 6)
  else "NOAXIOM"

fun get_location_aux line =
  let val p1 = char_place "(" line in
  let val p2 = char_place "," line in
    String.substring (line,p1+1,p2-p1-1)
  end end
 
fun get_location line =
  let val str = get_location_aux line in
  let val l = split_char "s" str in
    map string_to_int l
  end end

fun get_rule line =
  let val p1 = char_place "(" line in
  let val p2 = char_place "," line in
    String.substring (line,p1+1,p2-p1-1)
  end end
  
(* test
val line = "    ($lesseq(0, xx)),";
val line = "tff(15s37s0,plain,(";
val line = "    inference(Unknown,[status(thm)],[])).";
*)

fun read_proof_aux linel rdict =
    case linel of
    [] => []
  | [s] => []
  | [s1,s2] => []
  | s1 :: s2 :: s3 :: m =>
      if not (success (first_n_char 4) s1) 
      then read_proof_aux (tl linel) rdict
      else if not (first_n_char 4 s1 = "tff(") 
      then read_proof_aux (tl linel) rdict
      else (get_location s1, read_tffclause (get_tffclause s2) rdict) :: 
           read_proof_aux m rdict


fun read_proof filepath dict = read_proof_aux (readl filepath) (mk_rdict dict)

          
end