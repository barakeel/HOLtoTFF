structure blibPrinter :> blibPrinter =
struct

open HolKernel Abbrev boolLib blibTools blibExtract blibName intSyntax

(* Free variables are in the dictionary cadict *)
(***** TFF *****)
(* tools *)

fun out file str = TextIO.output (file,str)

fun symb term =
  if is_conj term          then "&" 
  else if is_disj term     then "|"
  else if is_imp_only term then "=>" 
  else if is_neg term      then "~"
  else if is_forall term   then "!"
  else if is_exists term   then "?"
  else if is_eq term       then "="  
  else if is_negated term  then "$uminus"
  else if is_plus term     then "$sum"
  else if is_minus term    then "$difference"
  else if is_linmult term  then "$product"
  else if is_less term     then "$less"
  else if is_leq term      then "$lesseq"
  else if is_great term    then "$greater"
  else if is_geq term      then "$greatereq"
  else raise B_ERR "symb" ""


val commentline =
"%----------------------------------------------------------------------------"
fun tff s1 s2 s3 = 
  "tff(" ^ s1 ^ "_" ^ s2 ^ "," ^ s2 ^ ",(\n    " ^ s3 ^ " )).\n\n"

(* term *)
fun adj_tffty bvdict tyadict bv = 
  assoc bv bvdict ^ ": " ^ assoc (type_of bv,0) tyadict          
fun ptff_qbvl bvdict tyadict qbvl = 
  "[" ^ (concats "," (map (adj_tffty bvdict tyadict) qbvl)) ^ "]"           

fun name_int term =     
  if is_negated term 
  then symb term ^ "(" ^ name_int (dest_negated term) ^ ")"
  else term_to_string term

fun ptff_t dict pflag bvl term =
  if is_int_literal term then name_int term
  else if is_var term then
    if mem term bvl then (assoc term (#2 dict)) else (assoc term (#3 dict))
  else if is_const term then 
    if term = T      then (if pflag then "$true"  else "btrue")
    else if term = F then (if pflag then "$false" else "bfalse")
    else assoc term (#3 dict)
  else if is_eq term    then ptff_binop dict false bvl term
  else if is_binop term then ptff_binop dict pflag bvl term
  else if is_unop term  then ptff_unop  dict pflag bvl term
  else if is_quant term then ptff_quant dict pflag bvl term
  else if is_bina term then ptff_app (symb term) dict false bvl [lhand term,rand term]
  else if is_una term then ptff_app (symb term) dict false bvl [rand term]
  else if is_comb term  then
    let val (oper,argl) = strip_comb term in
      if is_var oper then  
        if mem oper bvl
        then ptff_app (assoc oper (#2 dict)) dict false bvl argl
        else ptff_app (assoc oper (#3 dict)) dict false bvl argl
      else if is_const oper then
        ptff_app (assoc oper (#3 dict)) dict false bvl argl 
      else raise B_ERR "ptff_t" ""
    end
  else raise B_ERR "ptff_t" ""
and ptff_argl dict pflag bvl argl = concats "," (map (ptff_t dict pflag bvl) argl) 
and ptff_unop dict pflag bvl term =
  symb term ^ "(" ^ ptff_t dict pflag bvl (rand term) ^ ")"
and ptff_binop dict pflag bvl term = 
  "(" ^ ptff_t dict pflag bvl (lhand term) ^ " " ^ symb term ^ " " ^
  ptff_t dict pflag bvl (rand term) ^ ")"
and ptff_quant dict pflag bvl term = 
  let val (qbvl,t) = strip_quant term in
    "( " ^ symb term ^ " " ^ ptff_qbvl (#2 dict) (#1 dict) qbvl ^
    " : " ^  ptff_t dict pflag (qbvl @ bvl) t ^ " )"
  end
and ptff_app str dict pflag bvl argl = str ^ "(" ^ ptff_argl dict pflag bvl argl ^ ")"

fun ptff_term dict term = ptff_t dict true [] term 

(* type *)
fun tffty nm tynm = tff nm "type" (nm ^ ": " ^ tynm) 
fun ptff_tya ((ty,a),nm) = if nm <> "$int" then tffty nm "$tType" else ""
fun wtff_tyadict file tyadict = app ((out file) o ptff_tya) tyadict


(* constants *)  
fun ptff_ca tyadict ((c,a),cnm) = 
  let val (argl,im) = strip_type_n (type_of c,a) in
  let val argnml = map (inv assoc tyadict) argl in
  let val imnm = if fst im = bool then "$o" else assoc im tyadict in
    case argnml of 
      []      => tffty cnm (assoc im tyadict)
    | [argnm] => tffty cnm (argnm ^ " > " ^ imnm)
    | _       => tffty cnm ("( " ^ concats " * " argnml ^ " ) > " ^ imnm)
  end end end
 
(* axioms *)
fun ptff_axiom dict (term,name) = tff name "axiom" (ptff_term dict term)

(* problem *)
fun out_tff file goal =
  let val term = list_mk_conj (snd goal :: fst goal) in
  let 
    val tyadict = create_tyadict term
    val bvdict  = create_bvdict term  
    val cadict  = create_cadict term 
  in
  let fun drop_arity ((c,a),nm) = (c,nm) in
  let val dict = (tyadict,bvdict,map drop_arity cadict) in
    (
    out file (commentline ^ "\n");
    out file (tffty "ty_bool" "$tType");
    app ((out file) o ptff_tya) tyadict;
    app ((out file) o (ptff_ca tyadict)) cadict;
    out file (tffty "btrue" "ty_bool");
    out file (tffty "bfalse" "ty_bool");
    out file (tff "ty_bool" "axiom" "~(btrue = bfalse)");
    app ((out file) o (ptff_axiom dict)) 
      (combine ((fst goal),(numl "axiom" (length (fst goal)))));
    out file (tff "conjecture" "conjecture" (ptff_term dict (snd goal)));
    out file (commentline ^ "\n")
    )
  end end end end

fun write_tff path goal =
  let val file = TextIO.openOut path handle _ => raise B_ERR "write_tff" path in
    (out_tff file goal; TextIO.closeOut file)
  end
  
end