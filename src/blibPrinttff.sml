structure blibPrinttff :> blibPrinttff =
struct

open HolKernel Abbrev boolLib HOLPP
     blibBtools blibDatatype 
     blibSyntax blibTffsyntax blibPredicate
     blibExtractvar blibExtracttype blibNamevar blibNametype blibHO
     beagleStats

fun PRINTTFF_ERR function message =
  HOL_ERR{origin_structure = "blibPrinttff",
          origin_function = function,
          message = message}


(* bad hack NLIA *)
fun contain_numfvc term = not (null (filter has_numty (get_fvcl term)))
fun linear term =
  case nodeconst term of
    Mult => not (contain_numfvc (rand term) andalso contain_numfvc (lhand term))
  | _    => raise PRINTTFF_ERR "linear" "not a product"

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
  case termstructure term of
    Numeral => add_string pps (name_of term)
  | Var => if is_member_aconv term bvl
           then add_string pps (lookup term (#2 dict)) (*boundvar*)
           else add_string pps (lookup term (#3 dict)) (*freevar*)
  | Const => 
    (
    case leafconst term of
      False => if pflag
               then add_string pps "$false"
               else add_string pps "bfalse"
    | True => if pflag
              then add_string pps "$true"
              else add_string pps "btrue"
    | Newleafconst => add_string pps (lookup term (#4 dict))
    )
  | Comb => 
    (
    case connector term of  
      Conj => pptff_binop pps "&" term dict pflag bvl
    | Disj => pptff_binop pps "|" term dict pflag bvl
    | Neg => pptff_unop pps "~" term dict pflag bvl 
    | Imp_only => pptff_binop pps "=>" term dict pflag bvl
    | Forall => let val (qbvl,t) = strip_forall term in
                          pptff_quant pps "!" qbvl t dict pflag bvl
                        end       
    | Exists => let val (qbvl,t) = strip_exists term in
                          pptff_quant pps "?" qbvl t dict pflag bvl
                        end
    | App => 
      let val (operator,argl) = strip_comb term in
      let val arity = get_arity term in
      case termstructure operator of
        Numeral => raise PRINTTFF_ERR "pptff_term_aux" "numeral"
      | Var => if is_member_aconv operator bvl
               then pptff_app pps (lookup operator (#2 dict)) argl dict false bvl
               else pptff_app pps (lookup operator (#3 dict)) argl dict false bvl 
      | Const => 
        (
        case nodeconst term of
          Eq => pptff_binop pps "=" term dict false bvl
        | Mult => if linear term  (* bad hack NLIA *)
                  then pptff_app pps "$product" argl dict false bvl  
                  else pptff_app pps    
                    (lookup operator (#4 dict)) argl dict false bvl  
        | Newnodeconst => pptff_app pps 
                            (lookup operator (#4 dict)) argl dict false bvl                
        | _ => pptff_app pps 
                 (lookup (nodeconst term) dcdict) argl dict false bvl
        ) 
      | _ => raise PRINTTFF_ERR "pptff_term_aux" "abs or comb"
      end end  
    )
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
  pptff_term_aux pps (rand term) dict pflag bvl
  )
and pptff_binop pps str term dict pflag bvl = 
  (
  add_string pps "(";
  pptff_term_aux pps (lhand term) dict pflag bvl;
  add_string pps (" " ^ str ^ " ");
  pptff_term_aux pps (rand term) dict pflag bvl;
  add_string pps ")"
  )
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

fun pptff_number pps nb =
 (add_string pps ( "% Number   : " ^ (Int.toString (fst nb)) );  
  add_newline pps)


fun has_simplety ((ty,arity),name) = (arity = 0)
fun get_simpletyadict tyadict = filter has_simplety tyadict


(* test  
name_of (rator (rator ``a <= b``));
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
  pptff_type pps "btrue" "bool";
  nl2 pps;
  pptff_type pps "bfalse" "bool";
  nl2 pps 
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

fun pptff_axioml_aux pps terml dict start =
  case terml of
    [] => ()
  | t :: m =>  
    (
    pptff_axiom pps ("axiom" ^ (Int.toString start)) t dict;
    pptff_axioml_aux pps m dict (start + 1)
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

fun pptff_tff_w pps nb goal =
  let val terml = (fst goal) @ [snd goal] in
  let val term = list_mk_conj (terml) in 
  (* this term is only there to extract variables from *)
  let 
    (* free variables or constant *)
    val bval = get_bval term
    val fval = get_fval term
    val cal = get_cal term
    val fvcal = get_fvcal term
  in  
    if firstorder_err term (* raise an exception *)
    then 
      let 
      (* dict *)
        val tyadict = create_tyadict term
        val simpletyadict = erase_dtyname (get_simpletyadict tyadict)
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
        pptff_number pps nb;
        pptff_commentline pps;
        pptff_tyadict pps simpletyadict;
        pptff_fvatydict pps fvdict fvatydict;
        pptff_catydict pps cdict (filter (not o is_dcaty2) catydict);
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
fun pptff_tff pps nb goal = 
  wrap "blibPrinttff" "pptff_tff" "" (pptff_tff_w pps nb) goal


(* OUTPUT TFF *)
fun write_tff_w path nb goal appendflag =
  let val file = 
    if appendflag then TextIO.openAppend path else TextIO.openOut path in 
  let val pps = mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 80,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in 
    (
    let val dict = pptff_tff pps nb goal in
      (TextIO.closeOut file; dict)
    end
    )  
  end end
fun write_tff path nb goal appendflag = 
  wrap "blibPrinttff" "write_tff" "" (write_tff_w path nb goal) appendflag
 
  
(* test
val thm = ;
val path = ;
*)


end



