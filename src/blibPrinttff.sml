structure blibPrinttff :> blibPrinttff =
struct

open HolKernel Abbrev boolLib HOLPP
     blibBtools blibDatatype 
     blibSyntax blibTffsyntax blibPredicate
     blibExtractvar blibExtracttype blibNamevar blibNametype blibHO

fun PRINTTFF_ERR function message =
  HOL_ERR{origin_structure = "blibPrinttff",
          origin_function = function,
          message = message}

(* PPTFF_TERM *)
fun pptff_qbvl_aux pps qbvl bvdict tyadict  =
  case qbvl of
    [] => raise PRINTTFF_ERR "pptff_bvl_aux" "emptylist"
  | [qbv] => ( 
            add_string pps (lookup qbv bvdict); 
            add_string pps ": ";
            add_string pps (lookup (type_of qbv,0) tyadict)
            ) 
  | qbv :: m => (
               add_string pps (lookup qbv bvdict); 
               add_string pps ": ";
               add_string pps (lookup (type_of qbv,0) tyadict); 
               add_string pps ","; 
               pptff_qbvl_aux pps m bvdict tyadict
               )  

fun pptff_qbvl pps qbvl bvdict tyadict = 
  (
  add_string pps "[";
  pptff_qbvl_aux pps qbvl bvdict tyadict;
  add_string pps "]"
  )             
(* 
#1 dict : list of ((type,arity), its name) 
#2 dict : list of (bound variable, its name) 
#3 dict : list of (free variable, its name)  
#4 dict : list of (constant, its name) 
*)
(* pflag : flag is turn off when going inside atom *)
fun pptff_term_aux pps term dict pflag bvl =
  case structterm term of
    Numeral => add_string pps (namev_of term)
  | Integer => add_string pps (namev_of term)
  | Var => if is_member_aconv term bvl
           then add_string pps (lookup term (#2 dict)) (* boundvar *)
           else add_string pps (lookup term (#3 dict)) (* freevar *)
  | Const => 
    (
    case structleafc term of
      False => if pflag then add_string pps "$false"
                        else add_string pps "bfalse"
    | True => if pflag then add_string pps "$true"
                       else add_string pps "btrue"
    | Otherleafc => add_string pps (lookup term (#4 dict))
    )
  | Comb => 
    (
    case structcomb term of
      Eq => pptff_binop_infix pps "=" term dict false bvl
    (* hack NLIA *)
    | Multn => if linearn term  
               then pptff_binop_prefix pps
                      (op_symb term) term dict false bvl  
               else pptff_binop_prefix pps    
                 (lookup (fst (strip_comb term)) (#4 dict)) term dict false bvl
    | Multi => if lineari term  
               then pptff_binop_prefix pps
                      (op_symb term) term dict false bvl  
               else pptff_binop_prefix pps    
                 (lookup (fst (strip_comb term)) (#4 dict)) term dict false bvl
    (* end hack NLIA *)
    | _ =>
    ( 
    case structarity term of
      Binop => 
        (
        case structinfix term of
          Infix => pptff_binop_infix pps (op_symb term) term dict pflag bvl
        | Prefix => pptff_binop_prefix pps (op_symb term) term dict pflag bvl
        | _ => raise PRINTTFF_ERR "pptff_term_aux" "neither prefix nor infix"
        )
    | Unop => pptff_unop pps (op_symb term) term dict pflag bvl
    | Quant => let val (qbvl,t) = strip_quant term in
                 pptff_quant pps (op_symb term) qbvl t dict pflag bvl
               end
              
    | _ => 
      let val (operator,argl) = strip_comb term in
      let val arity = get_arity term in
      case structterm operator of
        Numeral => raise PRINTTFF_ERR "pptff_term_aux" "numeral"
      | Integer => raise PRINTTFF_ERR "pptff_term_aux" "integer"
      | Var => if is_member_aconv operator bvl
               then pptff_app pps (lookup operator (#2 dict)) argl dict false bvl
               else pptff_app pps (lookup operator (#3 dict)) argl dict false bvl 
      | Const => pptff_app pps (lookup operator (#4 dict)) argl dict false bvl    
      | _ => raise PRINTTFF_ERR "pptff_term_aux" "abs or comb"
      end end  
    ))
  | Abs => raise PRINTTFF_ERR "pptff_term_aux" "abs"
  handle _ => raise PRINTTFF_ERR "pptff_term_aux" ""
and pptff_argl pps argl dict pflag bvl = 
  case argl of
    [] => raise PRINTTFF_ERR "pptff_argl" "emptylist"
  | [arg] => pptff_term_aux pps arg dict pflag bvl
  | arg :: m => 
    ( 
    pptff_term_aux pps arg dict pflag bvl; 
    add_string pps ",";
    pptff_argl pps m dict pflag bvl
    ) 
and pptff_unop pps str term dict pflag bvl =
  (
  add_string pps str;
  add_string pps "(";
  pptff_term_aux pps (rand term) dict pflag bvl;
  add_string pps ")"
  )
and pptff_binop_infix pps str term dict pflag bvl = 
  (
  add_string pps "(";
  pptff_term_aux pps (lhand term) dict pflag bvl;
  add_string pps (" " ^ str ^ " ");
  pptff_term_aux pps (rand term) dict pflag bvl;
  add_string pps ")"
  )
and pptff_binop_prefix pps str term dict pflag bvl =
  pptff_app pps str [lhand term, rand term] dict pflag bvl    
and pptff_quant pps str qbvl term dict pflag bvl = 
  (
  add_string pps (str ^ " ");
  pptff_qbvl pps qbvl (#2 dict) (#1 dict);
  add_string pps " : ";  
  add_string pps "("; 
  pptff_term_aux pps term dict pflag (qbvl @ bvl);
  add_string pps ")" 
  )
and pptff_app pps str argl dict pflag bvl =
  (
  add_string pps str;
  add_string pps "(";
  pptff_argl pps argl dict pflag bvl; 
  add_string pps ")"
  )  

fun pptff_term pps term dict = 
  wrap "blibPrinttff" "pptff_term" (term_to_string term)
  (pptff_term_aux pps term dict true) []

(* PRINT_TFF *)
(* useful functions *)
fun nl2 pps = (add_newline pps; add_newline pps) 
fun indent4 pps = ((* to be replaced with begin block maybe *)
                    add_newline pps; 
                    add_string pps (space 4)
)

fun pptff_commentline pps =
  (add_string pps 
"%----------------------------------------------------------------------------"
  ; 
  add_newline pps
  )


fun has_simplety ((ty,arity),name) = (arity = 0)
fun get_simpletyadict tyadict = filter has_simplety tyadict


(* test  
namev_of (rator (rator ``a <= b``));
*)

(* end useful functions *)

(* TYPE *)

fun pptff_type pps name tyname =
  ( 
  add_string pps ("tff(" ^ name ^ "_type,type,(");
  indent4 pps;
  add_string pps (name ^ ": " ^ tyname ^ " )).")
  ) 
  (* argument should only be the simpletyadict *)
fun pptff_tyadict pps tyadict =
   case tyadict of
    [] => ()
  | ((ty,a),name) :: m => 
    (
    pptff_type pps name "$tType";
    nl2 pps;
    pptff_tyadict pps m
    )
    
(* free variables *)  
fun pptff_fvatydict pps fvdict fvatydict =
  case fvatydict of
    [] => () 
  | ((fv,arity),tyname) :: m => 
    (
    pptff_type pps (lookup fv fvdict) tyname;
    nl2 pps;
    pptff_fvatydict pps fvdict m
    )
 
fun pptff_catydict pps cdict catydict =
  case catydict of
    [] => () 
  | ((c,arity),tyname) :: m => 
    ( 
    pptff_type pps (lookup c cdict) tyname;
    nl2 pps;
    pptff_catydict pps cdict m
    )

(* boolean *)
fun pptff_btrue_bfalse pps =
  (
  pptff_type pps "btrue"  "bool"; nl2 pps;
  pptff_type pps "bfalse" "bool"; nl2 pps 
  )

(* AXIOM *)
fun pptff_axiom pps name term dict =
  ( 
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  pptff_term pps term dict;
  add_string pps " )).";
  nl2 pps
  ) 

fun pptff_axioml_aux pps terml dict n =
  case terml of
    [] => ()
  | t :: m =>  
    (
    pptff_axiom pps ("axiom" ^ (Int.toString n)) t dict;
    pptff_axioml_aux pps m dict (n + 1)
    )

fun pptff_axioml pps terml dict = pptff_axioml_aux pps terml dict 1;      
    
fun pptff_conjecture pps name term dict =
  if term = F then ()
  else
    ( 
    add_string pps ("tff(" ^ name ^ "_conjecture,conjecture,(");
    indent4 pps;
    pptff_term pps term dict;
    add_string pps " )).";
    nl2 pps
    )

fun is_tffdty str = first_n_char 1 str = "$" 
fun test_tffdty ((ty,a),str) = is_tffdty str

fun pptff_tff_w pps goal =
  let val terml = (fst goal) @ [snd goal] in
  let val term = list_mk_conj (terml) in  (* trick to extract variables *)
  let 
    (* free variables or constants *)
    val bval = get_bval term
    val fval = get_fval term
    val cal = get_cal term
    val fvcal = get_fvcal term
  in  
    if firstorder_err term (* raise an exception if the term is not first order *)
    then 
      let 
        (* dictionnaries *)
        val tyadict = create_tyadict term
        val simpletyadict = get_simpletyadict tyadict
        val bvdict = create_bvdict term  
        val bvatydict = create_bvatydict term tyadict
        val fvdict = create_fvdict term 
        val fvatydict = create_fvatydict term tyadict
        val cdict = create_cdict term 
        val catydict = create_catydict term tyadict
      in
      let val dict = (tyadict,bvdict,fvdict,cdict) in
      (
      begin_block pps CONSISTENT 0;
        pptff_commentline pps;
        pptff_tyadict pps (filter (not o test_tffdty) simpletyadict);
        pptff_fvatydict pps fvdict fvatydict;
        pptff_catydict pps cdict catydict;
        if has_boolarg term then pptff_btrue_bfalse pps else ();
        pptff_axioml pps (fst goal) dict;
        pptff_conjecture pps "conjecture" (snd goal) dict;
        pptff_commentline pps;
        add_string pps "\n";
      end_block pps;
      dict
      )
      end end
    else raise PRINTTFF_ERR "higher_order" ""
  end end end 
fun pptff_tff pps goal = 
  wrap "blibPrinttff" "pptff_tff" "" (pptff_tff_w pps) goal

(* WRITE A TFF FILE *)
fun write_tff path goal =
  (
  let val file = TextIO.openOut path in 
  let val pps = mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 80,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in 
    (
    let val dict = pptff_tff pps goal in
      (TextIO.closeOut file; dict)
    end
    )  
  end end
  )
  handle _ => raise PRINTTFF_ERR "write_tff" path

 

end



