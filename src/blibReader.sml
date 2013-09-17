structure blibReader :> blibReader =
struct

open HolKernel Abbrev boolLib
     blibBtools
     blibSyntax blibTffsyntax blibFreshvar
     beaglePrintresult
     
fun READER_ERR function message =
  HOL_ERR{origin_structure = "blibReader",
          origin_function = function,
          message = message}
 
(* TOOLS *) 
fun first_n_char n str = String.substring (str,0,n)
fun erase_n_char n str = String.substring (str,n,String.size str - n)
fun last_char str = String.substring (str,String.size str -1,1)
(* test
erase_n_char 1 "hello";
last_char "hello";
*)

fun char_place_aux ch str n =
  if first_n_char 1 str = ch then n
  else char_place_aux ch (erase_n_char 1 str) (n + 1)
fun char_place ch str = char_place_aux ch str 0

fun char_in ch str = success (char_place ch) str 
(* test
char_in "," "hel,lo";
*)
fun split_char ch str =  
  if char_in ch str  
  then
    let val p = char_place ch str in
      first_n_char p str :: 
      split_char ch (erase_n_char (p+1) str)  
    end
  else [str]

fun number_par_aux charl n =
  case charl of
    [] => []
  | c :: m => case Char.toString c of
               "(" => ("(",n + 1) :: number_par_aux m (n + 1)
              | ")" => (")",n) :: number_par_aux m (n - 1)
              | _   => (" ",n) :: number_par_aux m n

fun number_par str = number_par_aux (String.explode str) 0

(* test 
number_par "()5(()";
val str = "()5(()";*)

fun is_closebefore str =
  is_member (")",1) (tl (rev (number_par str))) 

fun erase_par str =
  if first_n_char 1 str = "(" andalso last_char str = ")" andalso
  not (is_closebefore str)
  then String.substring (str,1,String.size str - 2)
  else str

fun erase_spaces str =
  if str = "" then ""
  else
    if first_n_char 1 str = " "
    then erase_spaces (erase_n_char 1 str)
    else (first_n_char 1 str) ^ (erase_spaces (erase_n_char 1 str))
  
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
     split_char "," (erase_par (erase_n_char p tffterm))
  end
  
fun remember_var tffvar dict = 
  if is_member tffvar (map fst dict) 
  then lookup tffvar dict
  else mk_var (tffvar,``:num``)

(* need to care after defined constant too *)
fun is_tffvar tffterm = 
  is_upperword tffterm orelse is_lowerword tffterm

(* do something more for constants dictionnary*)    
fun read_tffterm tffterm dict =
  if is_tffvar tffterm 
  then remember_var tffterm dict
  else 
    let val oper = remember_var (get_tffoperator tffterm) dict in 
    let val tffargl = get_tffargl tffterm in
      list_mk_comb (oper,map (inv read_tffterm dict) tffargl)
    end end

fun read_tfflit tfflit dict =
  let val lit = erase_par tfflit in
    if char_in "~" lit
    then mk_neg (read_tfflit (erase_n_char 1 lit) dict)
    else 
      if not (char_in "=" lit) then read_tffterm lit dict
      else if not (char_in "!" lit) then
        let val p = char_place "=" lit in
        let val t1 = first_n_char p lit in
        let val t2 = erase_n_char (p+1) lit in 
          mk_eq (read_tffterm t1 dict,read_tffterm t2 dict)
        end end end
      else
        let val p = char_place "!" lit in
        let val t1 = first_n_char p lit in
        let val t2 = erase_n_char (p+2) lit in 
          mk_neg (mk_eq (read_tffterm t1 dict,read_tffterm t2 dict))
        end end end
  end

fun read_tffdisj tffdisj dict =
  let val disj = erase_par tffdisj in
    if not (char_in "|" disj) then read_tfflit disj dict
    else
      let val p = char_place "|" disj in
      let val lit = first_n_char p disj in
      let val disjright = erase_n_char (p+1) disj in 
        mk_disj (read_tfflit lit dict, read_tffdisj disjright dict) 
      end end end
  end

(* create the bvdict *)
fun prep_tffbvl clause =
  let val p1 = char_place "[" clause in
  let val p2 = char_place "]" clause in
    split_char "," (String.substring (clause,p1 + 1,p2 - p1 - 1))
  end end
 
fun mk_bventry arg = 
  case arg of
    [str1,str2] => (str1,mk_var (str1,``:num``))
  | _           => raise READER_ERR "mk_var_ss" ""

fun mk_bvdict clause =
  let val tffbvl = prep_tffbvl clause in
  let val tffbvl2 = map (split_char ":") tffbvl in
    map mk_bventry tffbvl2
  end end

    
fun get_tffdisj clause = 
  let val p = char_place "]" clause in
    String.substring (clause, p + 2, String.size clause - p - 2)
  end  
    
fun read_tffclause tffclause dict =
  let val clause = erase_par tffclause in
    if not (char_in "[" clause) then read_tffdisj clause dict
    else
      let val tffdisj = get_tffdisj clause in
      let val bvdict = mk_bvdict clause in
      let val bvl = map snd bvdict in
        list_mk_forall (bvl,read_tffdisj tffdisj dict)
      end end end
  end

(* test
val tfflit = "(f(x,y))";
val tffdisj = "(f(x,y)=f(a,b))|~(y=x)";
val tffclause = "![x:$int,y:$int]:((f(x,y)=f(a,b))|~(y=x))";
val dict= [("f",mk_var ("f",``:num -> num -> bool``))];

read_tffclause tffclause dict;
*)

(* READ FILE *)
fun is_intro line = 
  if success (first_n_char 4) line
  then first_n_char 4 line = "tff("
  else false
  
fun get_intro_aux line =
  let val p1 = char_place "," line in
  let val p2 = char_place "," (erase_n_char (p1 + 1) line) in
    String.substring (line,p1 + 1, p2)
  end end

fun get_intro line =
  if success get_intro_aux line 
  then get_intro_aux line 
  else "NOINFO"
(* test
get_introinfo "hel,lo,bon";
*)

fun get_tffclause line = 
  if success String.substring (line,4,String.size line - 6)
  then (erase_spaces o erase_par) 
         (String.substring (line,4,String.size line - 6))
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
   
(* test
val line = "    ($lesseq(0, xx)),";
val line = "tff(15s37s0,plain,(";
*)

fun read_axioml linel =
    case linel of
    [] => []
  | [s] => []
  | [s1,s2] => []
  | s1 :: s2 :: s3 :: m =>
      if get_intro s1 = "axiom" 
      then (read_tffclause (get_tffclause s2),get_location s1)
      else read_axioml (tl linel)

fun read_proof linel = 
  case linel of
    [] => []
  | [s] => []
  | [s1,s2] => []
  | s1 :: s2 :: s3 :: m =>
      if get_intro s1 = "plain"
      then (read_tffclause (get_tffclause s2),get_location s1)
      else read_proof (tl linel)
 
fun is_ascendant nl1 nl2 =
  if length nl1 <= length nl2
  then
    case nl1 of
      [] => false
    | [n] => true
    | _ => hd nl1 = hd nl2 andalso is_ascendant (tl nl1) (tl nl2)
  else false

fun is_ascendant_cln (cl1,nl1) (cl2,nl2) = is_ascendant nl1 nl2

fun get_ascendants cln proofbf = 
  filter (inv is_ascendant_cln cln) proofbf 


(* difficulty with splits *)    
fun replayproof tobeproved provedl =
  case tobeproved of 
    | [] => if success DECIDE_TAC (provedl,F)
            then 
    | cln :: m => 
        let val clnl = get_ascendant_cln cln in  
          Prove (clnl,cln) , replayproof tobeproved2 provedl1
        end


 
  
          
end