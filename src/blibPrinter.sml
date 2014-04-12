structure blibPrinter :> blibPrinter =
struct

open HolKernel Abbrev boolLib blibTools blibName blibConv

(* pflag : flag is turn off when going inside atom *)
(* tools *)
fun out file str = TextIO.output (file,str)
fun outl file strl = app (out file) strl

fun op_symb term =
  if is_conj term then "&" 
  else if is_disj term then "|"
  else if is_imp_only term then "=>" 
  else if is_neg term then "~"
  else if is_forall term then "!"
  else if is_exists term then "?"
  else if is_eq term then "=" 
  else raise B_ERR "op_symb" ""

val commentline =
"%----------------------------------------------------------------------------"
 
fun tff s1 s2 s3 = 
  "tff(" ^ s1 ^ "_" ^ s2 ^ "," ^ s2 ^ ",(\n    " ^ s3 ^ " )).\n\n"
fun fof s1 s2 s3 =
  "fof(" ^ s1 ^ "_" ^ s2 ^ "," ^ s2 ^ ",(\n    " ^ s3 ^ " )).\n\n"

(***** TFF *****)
(* term *)
fun adj_type bvdict tyadict bv = 
  assoc bv bvdict ^ ": " ^ assoc (type_of bv,0) tyadict          
fun ptff_qbvl qbvl bvdict tyadict = 
  "[" ^ (concats "," (map (adj_type bvdict tyadict) qbvl)) ^ "]"           

fun ptff_t term dict pflag bvl =
  if is_var term then
    if mem term bvl then (assoc term (#2 dict)) else (assoc term (#3 dict))
  else if is_const term then 
    if term = T      then (if pflag then "$true" else "btrue")
    else if term = F then (if pflag then "$false" else "bfalse")
    else (assoc term (#4 dict))
  else if is_eq term then ptff_binop term dict false bvl
  else if is_binop term then ptff_binop term dict pflag bvl
  else if is_unop term then ptff_unop term dict pflag bvl
  else if is_quant term then ptff_quant term dict pflag bvl
  else if is_comb term then
    let val (operator,argl) = strip_comb term in
    let val arity = List.length argl in
      if is_var operator then  
        if mem operator bvl
        then ptff_app (assoc operator (#2 dict)) argl dict false bvl
        else ptff_app (assoc operator (#3 dict)) argl dict false bvl 
      else if is_const operator then
        ptff_app (assoc operator (#4 dict)) argl dict false bvl    
      else raise B_ERR "ptff_t" ""
    end end  
  else raise B_ERR "ptff_t" ""
and ptff_argl argl dict pflag bvl = 
  case argl of
    [] => raise B_ERR "ptff_t" ""
  | [arg] => ptff_t arg dict pflag bvl
  | arg :: m => ptff_t arg dict pflag bvl ^ "," ^ ptff_argl m dict pflag bvl
and ptff_unop term dict pflag bvl =
  op_symb term ^ "(" ^ ptff_t (rand term) dict pflag bvl ^ ")"
and ptff_binop term dict pflag bvl = 
  "(" ^ ptff_t (lhand term) dict pflag bvl ^ 
  (" " ^ op_symb term ^ " ") ^
  ptff_t (rand term) dict pflag bvl ^ ")"
and ptff_binop_prefix str term dict pflag bvl =
  ptff_app str [lhand term, rand term] dict pflag bvl    
and ptff_quant term dict pflag bvl = 
  let val (qbvl,t) = strip_quant term in
    "( " ^ op_symb term ^ " " ^ ptff_qbvl qbvl (#2 dict) (#1 dict) ^
    " : " ^  ptff_t t dict pflag (qbvl @ bvl) ^ " )"
  end
and ptff_app str argl dict pflag bvl =
  str ^ "(" ^ ptff_argl argl dict pflag bvl ^ ")"

fun ptff_term term dict = ptff_t term dict true []

(* type *)
fun tffty nm tynm = tff nm "type" (nm ^ ": " ^ tynm) 
fun ptff_tya ((ty,a),nm) = tffty nm "$tType"
fun wtff_tyadict file tyadict = outl file (map ptff_tya tyadict)

(* free vars *)  
fun ptff_fva fvdict ((fv,a),nm) = tffty (assoc fv fvdict) nm;
fun wtff_fvatydict file fvdict fvatydict = outl file (map (ptff_fva fvdict) fvatydict)

(* constants *) 
fun ptff_ca cdict ((c,a),nm) = tffty (assoc c cdict) nm;
fun wtff_catydict file cdict catydict = outl file (map (ptff_ca cdict) catydict)

(* boolean *)
fun wtff_booldecl file =
  (
  out file (tffty "btrue" "ty_bool");
  out file (tffty "bfalse" "ty_bool");
  out file (tff "bool" "axiom" "~(btrue = bfalse)")
  )

(* axioms *)
fun wtff_axioml file terml dict n =
  case terml of
    [] => ()
  | t :: m =>  
     (
     out file (tff ("axiom" ^ Int.toString n) "axiom" (ptff_term t dict));
     wtff_axioml file m dict (n + 1)
     )
  
(* wtff tff file *)
fun out_tff file goal =
  let fun test ((ty,a),str) = not (String.substring (str,0,1) = "$") in
  let val term = list_mk_conj (snd goal :: fst goal) in
  let 
    val tyadict = create_tyadict term
    val bvdict = create_bvdict term  
    val fvdict = create_fvdict term 
    val cdict = create_cdict term 
  in
  let
    val fvatydict = create_fvatydict term tyadict
    val catydict = create_catydict term tyadict
  in
  let val dict = (tyadict,bvdict,fvdict,cdict) in
    (
    out file (commentline ^ "\n");
    out file (tffty "ty_bool" "$tType");
    wtff_tyadict file (filter test tyadict);
    wtff_fvatydict file fvdict fvatydict;
    wtff_catydict file cdict catydict;
    wtff_booldecl file;
    wtff_axioml file (fst goal) dict 1;
    if snd goal <> F 
    then out file (tff "conjecture" "conjecture" (ptff_term (snd goal) dict))
    else ();
    out file (commentline ^ "\n")
    )
  end end end end end

fun write_tff path goal =
  let val file = TextIO.openOut path handle _ => raise B_ERR "write_tff" path in
    (out_tff file goal; TextIO.closeOut file)
  end
    
(***** FOF *****)
(* term *)
fun pfof_t term dict pflag bvl =
  if is_var term then
    if mem term bvl then (assoc term (#1 dict)) else (assoc term (#2 dict))
  else if is_const term then 
    if term = T      then (if pflag then "$true" else "btrue")
    else if term = F then (if pflag then "$false" else "bfalse")
    else (assoc term (#3 dict))
  else if is_eq term then pfof_binop term dict false bvl
  else if is_binop term then pfof_binop term dict pflag bvl
  else if is_unop term then pfof_unop term dict pflag bvl
  else if is_quant term then pfof_quant term dict pflag bvl
  else if is_comb term then
    let val (operator,argl) = strip_comb term in
    let val arity = List.length argl in
      if is_var operator then  
        if mem operator bvl
        then pfof_app (assoc operator (#1 dict)) argl dict false bvl
        else pfof_app (assoc operator (#2 dict)) argl dict false bvl 
      else if is_const operator then
        pfof_app (assoc operator (#3 dict)) argl dict false bvl    
      else raise B_ERR "pfof_t" ""
    end end  
  else raise B_ERR "pfof_t" ""
and pfof_argl argl dict pflag bvl = 
  case argl of
    [] => raise B_ERR "pfof_t" ""
  | [arg] => pfof_t arg dict pflag bvl
  | arg :: m => pfof_t arg dict pflag bvl ^ "," ^ pfof_argl m dict pflag bvl
and pfof_unop term dict pflag bvl =
  op_symb term ^ "(" ^ pfof_t (rand term) dict pflag bvl ^ ")"
and pfof_binop term dict pflag bvl = 
  "(" ^ pfof_t (lhand term) dict pflag bvl ^
   (" " ^ op_symb term ^ " ") ^
  pfof_t (rand term) dict pflag bvl ^ ")"  
and pfof_quant term dict pflag bvl = 
  let val (qbvl,t) = strip_quant term in
    "( " ^ op_symb term ^ " " ^ 
    "[" ^ concats "," (map (inv assoc (#1 dict)) qbvl) ^ "]" ^ " : " ^ 
    pfof_t t dict pflag (qbvl @ bvl) ^ " )"
  end
and pfof_app str argl dict pflag bvl =
  str ^ "(" ^ pfof_argl argl dict pflag bvl ^ ")"

fun pfof_term term dict = pfof_t term dict true []

(* axioms *)
fun wfof_axioml file terml dict n =
  case terml of 
    []     => ()
  | t :: m => 
    (
    out file (fof ("axiom" ^ Int.toString n) "axiom" (pfof_term t dict));
    wfof_axioml file m dict (n + 1)
    )
 
(* conjecture *)
fun out_fof file goal =
  let val term = list_mk_conj (snd goal :: fst goal) in
  let 
    val bvdict = create_bvdict term  
    val fvdict = create_fvdict term 
    val cdict = create_cdict term 
  in
  let val dict = (bvdict,fvdict,cdict) in
    (
    out file (commentline ^ "\n");
    out file (fof "bool" "axiom" "~(btrue = bfalse)");
    wfof_axioml file (fst goal) dict 1;
    if snd goal <> F 
    then out file (tff "conjecture" "conjecture" (pfof_term (snd goal) dict))
    else ();
    out file (commentline ^ "\n")
    )
  end end end

fun write_fof path goal =
  let val file = TextIO.openOut path handle _ => raise B_ERR "write_fof" path in
    (out_fof file goal; TextIO.closeOut file)
  end



end