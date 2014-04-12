structure blibPrinter :> blibPrinter =
struct

open HolKernel Abbrev boolLib blibTools blibName blibConv

(* 
#1 dict : list of ((type,arity), its name) 
#2 dict : list of (bound variable, its name) 
#3 dict : list of (free variable, its name)  
#4 dict : list of (constant, its name) 
pflag : flag is turn off when going inside atom 
*)

fun out (file,str) = TextIO.output (file,str)

(* Printing term *)
fun op_symb term =
  if is_conj term then "&" 
  else if is_disj term then "|"
  else if is_imp_only term then "=>" 
  else if is_neg term then "~"
  else if is_forall term then "!"
  else if is_exists term then "?"
  else if is_eq term then "=" 
  else raise B_ERR "op_symb" "not an tff operator"

fun print_qbvl_aux qbvl bvdict tyadict  =
  case qbvl of
    [] => raise B_ERR "print_bvl_aux" "emptylist"
  | [qbv] => assoc qbv bvdict ^ ": " ^ assoc (type_of qbv,0) tyadict
  | qbv :: m => 
     assoc qbv bvdict ^ ": " ^ assoc (type_of qbv,0) tyadict ^ "," ^
     print_qbvl_aux m bvdict tyadict
                 
fun print_qbvl qbvl bvdict tyadict = 
  "[" ^ print_qbvl_aux qbvl bvdict tyadict ^ "]"           

fun print_term_aux term dict pflag bvl =
  if is_var term then
    if mem term bvl 
    then (assoc term (#2 dict))
    else (assoc term (#3 dict))
  else if is_const term then 
    if term = T      then (if pflag then "$true" else "btrue")
    else if term = F then (if pflag then "$false" else "bfalse")
    else (assoc term (#4 dict))
  else if is_eq term then print_binop_infix (op_symb term) term dict false bvl
  else if is_binop term then print_binop_infix (op_symb term) term dict pflag bvl
  else if is_neg term then print_unop (op_symb term) term dict pflag bvl
  else if is_quant term then
    let val (qbvl,t) = strip_quant term in
      print_quant (op_symb term) qbvl t dict pflag bvl
    end
  else if is_comb term then
    let val (operator,argl) = strip_comb term in
    let val arity = List.length argl in
      if is_var operator then  
        if mem operator bvl
        then print_app (assoc operator (#2 dict)) argl dict false bvl
        else print_app (assoc operator (#3 dict)) argl dict false bvl 
      else if is_const operator then
        print_app (assoc operator (#4 dict)) argl dict false bvl    
      else raise B_ERR "print_term_aux" "abs or comb"
    end end  
  else raise B_ERR "print_term_aux" "abs"
and print_argl argl dict pflag bvl = 
  case argl of
    [] => raise B_ERR "print_argl" "emptylist"
  | [arg] => print_term_aux arg dict pflag bvl
  | arg :: m => print_term_aux arg dict pflag bvl ^ "," ^ print_argl m dict pflag bvl
and print_unop str term dict pflag bvl =
  "~(" ^ print_term_aux (rand term) dict pflag bvl ^ ")"
and print_binop_infix str term dict pflag bvl = 
  "(" ^ print_term_aux (lhand term) dict pflag bvl ^ 
  (" " ^ str ^ " ") ^
  print_term_aux (rand term) dict pflag bvl ^ ")"
and print_binop_prefix str term dict pflag bvl =
  print_app str [lhand term, rand term] dict pflag bvl    
and print_quant str qbvl term dict pflag bvl = 
  (str ^ " ") ^ print_qbvl qbvl (#2 dict) (#1 dict) ^
  " : " ^ "(" ^ print_term_aux term dict pflag (qbvl @ bvl) ^ ")"
and print_app str argl dict pflag bvl =
  str ^ "(" ^ print_argl argl dict pflag bvl ^ ")"

fun print_term term dict = print_term_aux term dict true []

(* Declaration *)
(* useful functions *)
val commentline =
"%----------------------------------------------------------------------------"

(* type *)
fun print_type name tyname =
  "tff(" ^ name ^ "_type,type,(" ^ "\n    " ^ name ^ ": " ^ tyname ^ " )).\n\n"
  
fun write_tyadict file tyadict =
  case tyadict of
    [] => ""
  | ((ty,a),name) :: m => 
      (out (file, print_type name "$tType");
      write_tyadict file m)

(* free vars *)  
fun write_fvatydict file fvdict fvatydict =
  case fvatydict of
    [] => () 
  | ((fv,arity),tyname) :: m => 
      (out (file,print_type (assoc fv fvdict) tyname);
       write_fvatydict file fvdict m)

(* constants *) 
fun write_catydict file cdict catydict =
  case catydict of
    [] => () 
  | ((c,arity),tyname) :: m => 
      (out (file,print_type (assoc c cdict) tyname);
      write_catydict file cdict m)

(* boolean *)
fun has_boolty term = type_of term = bool
fun has_boolarg term =
  let fun test t = not (is_var t orelse is_const t orelse is_abs t) in
  let val terml1 = filter test (find_atoml term) in
  let val terml2 = (map rand terml1) @ (map rator terml1) in
      exists (success (find_term has_boolty)) terml2
  end end end


fun write_booldecl file =
  (
  out (file, print_type "btrue" "ty_bool");
  out (file, print_type "bfalse" "ty_bool");
  out (file, "tff(bool_axiom,axiom,(\n    ~(btrue = bfalse))).\n\n")
  )

(* axioms *)
fun print_axiom name term dict =
  "tff(" ^ name ^ "_axiom,axiom,(\n    " ^ print_term term dict ^ " )).\n\n"

fun write_axioml file terml dict n =
  case terml of
    [] => ()
  | t :: m => 
    (out (file, print_axiom ("axiom" ^ (Int.toString n)) t dict);
     write_axioml file m dict (n + 1))
 
(* conjecture *)  
fun print_conjecture name term dict =
  if term = F then ""
  else "tff(" ^ name ^ "_conjecture,conjecture,(" ^
       "\n    " ^ print_term term dict ^ " )).\n\n" 

(* Write tff file *)
fun out_tff file goal =
  let fun test ((ty,a),str) = not (String.substring (str,0,1) = "$") in
  let val term = list_mk_conj (snd goal :: fst goal) in  (* trick to extract variables *)
  let 
    (* dictionnaries *)
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
    out (file, commentline ^ "\n");
    out (file, print_type "ty_bool" "$tType");
    write_tyadict file (filter test tyadict);
    write_fvatydict file fvdict fvatydict;
    write_catydict file cdict catydict;
    write_booldecl file;
    write_axioml file (fst goal) dict 1;
    out (file, print_conjecture "conjecture" (snd goal) dict);
    out (file, commentline ^ "\n")
    )
  end end end end end

fun write_tff path goal =
  let val file = TextIO.openOut path handle _ => raise B_ERR "write_tff" path in
    (out_tff file goal; TextIO.closeOut file)
  end
  

end