structure blibPrinter :> blibPrinter =
struct

open HolKernel Abbrev boolLib
     blibBtools 
     blibSyntax blibTffsyntax
     blibExtractvar blibExtracttype 
     blibNamevar blibNametype blibHO

(* 
#1 dict : list of ((type,arity), its name) 
#2 dict : list of (bound variable, its name) 
#3 dict : list of (free variable, its name)  
#4 dict : list of (constant, its name) 
pflag : flag is turn off when going inside atom 
*)

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
  | [qbv] => lookup qbv bvdict ^ ": " ^ lookup (type_of qbv,0) tyadict
  | qbv :: m => 
     lookup qbv bvdict ^ ": " ^ lookup (type_of qbv,0) tyadict ^ "," ^
     print_qbvl_aux m bvdict tyadict
                 
fun print_qbvl qbvl bvdict tyadict = 
  "[" ^ print_qbvl_aux qbvl bvdict tyadict ^ "]"           

fun print_term_aux term dict pflag bvl =
  if is_var term then
    if is_member term bvl 
    then (lookup term (#2 dict))
    else (lookup term (#3 dict))
  else if is_const term then 
    if term = T      then (if pflag then "$true" else "btrue")
    else if term = F then (if pflag then "$false" else "bfalse")
    else (lookup term (#4 dict))
  else if is_eq term then print_binop_infix "=" term dict false bvl
  else if is_binop term then print_binop_infix (op_symb term) term dict pflag bvl
  else if is_neg term then print_unop (op_symb term) term dict pflag bvl
  else if is_quant term then
    let val (qbvl,t) = strip_quant term in
      print_quant (op_symb term) qbvl t dict pflag bvl
    end
  else if is_comb term then
    let val (operator,argl) = strip_comb term in
    let val arity = get_arity term in
      if is_var operator then  
        if is_member operator bvl
        then print_app (lookup operator (#2 dict)) argl dict false bvl
        else print_app (lookup operator (#3 dict)) argl dict false bvl 
      else if is_const operator then
        print_app (lookup operator (#4 dict)) argl dict false bvl    
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
  add_string (" " ^ str ^ " ") ^
  print_term_aux (rand term) dict pflag bvl ^ ")"
and print_binop_prefix str term dict pflag bvl =
  print_app str [lhand term, rand term] dict pflag bvl    
and print_quant str qbvl term dict pflag bvl = 
  (str ^ " ") ^ print_qbvl qbvl (#2 dict) (#1 dict) ^
  " : " ^ "(" ^ print_term_aux term dict pflag (qbvl @ bvl) ^ ")"
and print_app str argl dict pflag bvl =
  str ^ "(" ^ print_argl argl dict pflag bvl ^ ")"

fun print_term term dict = 
  wrap "blibPrinter" "print_term" (term_to_string term)
  (print_term_aux term dict true) []

(* Declaration *)
(* useful functions *)
fun nl2 file = TextIO.output (file,"\n\n")
val commentline =
"%----------------------------------------------------------------------------"

(* type *)
fun print_type name tyname =
  "tff(" ^ name ^ "_type,type,(" ^
  ^ "\n    " ^ name ^ ": " ^ tyname ^ " ))."
  
(* argument should only be the simpletyadict *)
fun has_simplety ((ty,arity),name) = (arity = 0)
fun get_simpletyadict tyadict = filter has_simplety tyadict

fun write_tyadict file tyadict =
  case tyadict of
    [] => ""
  | ((ty,a),name) :: m => print_type name "$tType" ^ "\n\n" ^ print_tyadict m

    
(* free variables *)  
fun write_fvatydict file fvdict fvatydict =
  case fvatydict of
    [] => () 
  | ((fv,arity),tyname) :: m => 
      (TextIO.output (file,print_type (lookup fv fvdict) tyname);
       nl2 file;
       write_fvatydict file fvdict m)
 
fun write_catydict file cdict catydict =
  case catydict of
    [] => () 
  | ((c,arity),tyname) :: m => 
      (TextIO.output (file,print_type (lookup c cdict) tyname);
      nl2 file;
      write_catydict file cdict m)

(* boolean *)
fun write_booldecl file =
  (TextIO.output (file, print_type "btrue", "ty_bool");
   TextIO.output (file, print_type "btrue", "ty_bool"); 
   nl2 file)

(* axioms *)
fun print_axiom name term dict =
  "tff(" ^ name ^ "_axiom,axiom,(" ^
  ^ "\n    " ^ print_term term dict ^ " )).\n\n"

fun write_axioml file terml dict n =
  case terml of
    [] => ()
  | t :: m => 
    (TextIO.output(file, print_axiom ("axiom" ^ (Int.toString n)) t dict);
     write_axioml file m dict (n + 1))
 
(* conjecture *)  
fun print_conjecture name term dict =
  if term = F then ""
  else "tff(" ^ name ^ "_conjecture,conjecture,(" ^
       "\n    " ^ print_term term dict ^ " )).\n\n" 

(* Write tff file *)
fun print_tff file goal =
  let fun out str = TextIO.output (file,str) in
  let fun test ((ty,a),str) = not (first_n_char 1 str = "$") in
  let val terml = (fst goal) @ [snd goal] in
  let val term = list_mk_conj (terml) in  (* trick to extract variables *)
  let 
    (* free variables or constants *)
    val bval = get_bval term
    val fval = get_fval term
    val cal = get_cal term
  in  
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
    out commentline;
    write_tyadict file (filter test tyadict);
    write_fvatydict file fvdict fvatydict;
    write_catydict file cdict catydict;
    write_booldecl file;
    write_axioml file (fst goal) dict 1;
    out (print_conjecture "conjecture" (snd goal) dict);
    out (commentline ^ "\n")
    )
  end end end end end end end end

fun write_tff path goal =
  let val file = TextIO.openOut path in
    (print_tff goal;
     TextIO.closeOut file)
  end
  handle _ => raise B_ERR "write_tff" path

end