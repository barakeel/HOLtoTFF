structure printtff :> printtff =
struct
(*
load "listtools"; open listtools;
load "stringtools"; open stringtools;
load "mydatatype"; open mydatatype;
load "extractvar"; open extractvar;
load "extracttype"; open extracttype;
load "namevar"; open namevar;
load "nametype"; open nametype;
load "tools"; open tools;
open HOLPP; open numSyntax;
*)
open HolKernel Abbrev boolLib HOLPP numSyntax 
     tools
     stringtools listtools mydatatype
     extractvar extracttype namevar nametype higherorder

(* not all structures are necessary *)
fun PRINTTFF_ERR function message =
    HOL_ERR{origin_structure = "printtff",
            origin_function = function,
            message = message}

(*PRINT_TERM*)
fun pptff_bvl_aux pps bvl bvdict tyadict  =
  case bvl of
    [] => raise PRINTTFF_ERR "pptff_bvl_aux" "emptylist"
  | [bv] => ( 
            add_string pps (lookup bv bvdict); 
            add_string pps ": ";
            add_string pps (lookup (type_of bv,0) tyadict)
            ) 
  | bv :: m => (
               add_string pps (lookup bv bvdict); 
               add_string pps ": ";
               add_string pps (lookup (type_of bv,0) tyadict); 
               add_string pps ","; 
               pptff_bvl_aux pps m bvdict tyadict
               )  

fun pptff_bvl pps bvl bvdict tyadict = 
  (
  add_string pps "[";
  pptff_bvl_aux pps bvl bvdict tyadict;
  add_string pps "]"
  )
              
(* 
#1 dict : list of ((type,arity), its name) 
#2 dict : list of (bound variable, its name) 
#3 dict : list of (free variable, its name)  
#4 dict : list of (constant, its name) 
*)
(* dict isn't modified by pptff_term *)
(* pflag : predicateflag *)   
(* pflag only used for true or false *)
fun pptff_term pps term dict pflag =
  case termstructure term of
    Numeral => add_string pps (name_numeral term)
  | Var => if is_member term (map fst (#2 dict))
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
      Conj => pptff_binop pps "&" term dict pflag
    | Disj => pptff_binop pps "|" term dict pflag
    | Neg => pptff_unop pps "~" term dict pflag 
    | Imp_only => pptff_binop pps "=>" term dict pflag
    | Forall => let val (qbvl,t) = strip_forall term in
                          pptff_quant pps "!" qbvl t dict pflag
                        end       
    | Exists => let val (qbvl,t) = strip_exists term in
                          pptff_quant pps "?" qbvl t dict pflag
                        end
    | App => 
      let val (operator,argl) = strip_comb term in
      let val arity = get_arity term in
      case termstructure operator of
        Numeral => raise PRINTTFF_ERR "pptff_term" "numeral"
      | Var => if is_member operator (map fst (#2 dict))
               then pptff_app pps (lookup operator (#2 dict)) argl dict false
               else pptff_app pps (lookup operator (#3 dict)) argl dict false 
      | Const => 
        (
        case nodeconst term of
          Eq => pptff_binop pps "=" term dict false
        | Add => pptff_app pps "$sum" argl dict false
        | Minus => pptff_app pps "$difference" argl dict false 
        | Mult => pptff_app pps "$product" argl dict false  
        | Less => pptff_app pps "$less" argl dict false  
        | Greater => pptff_app pps "$greater" argl dict false  
        | Geq => pptff_app pps "$greatereq" argl dict false  
        | Leq => pptff_app pps "$lesseq" argl dict false
        | Newnodeconst => pptff_app pps 
                          (lookup operator (#4 dict)) argl dict false
        ) 
      | _ => raise PRINTTFF_ERR "pptff_term" "abs or comb"
      end end
      
    )
  | Abs => raise PRINTTFF_ERR "pptff_term" "abs"
  handle _ => raise PRINTTFF_ERR "pptff_term" ""
and pptff_argl pps argl dict pflag = 
  case argl of
    [] => raise PRINTTFF_ERR "pptff_argl" "emptylist"
  | [arg] => pptff_term pps arg dict pflag
  | arg :: m => 
    ( 
    pptff_term pps arg dict pflag; 
    add_string pps ",";
    pptff_argl pps m dict pflag
    ) 
and pptff_unop pps str term dict pflag =
  (
  add_string pps str;
  pptff_term pps (rand term) dict pflag
  )
and pptff_binop pps str term dict pflag = 
  (
  add_string pps "(";
  pptff_term pps (lhand term) dict pflag;
  add_string pps (" " ^ str ^ " ");
  pptff_term pps (rand term) dict pflag;
  add_string pps ")"
  )
and pptff_quant pps str bvl term dict pflag = 
  (
  add_string pps (str ^ " ");
  pptff_bvl pps bvl (#2 dict) (#1 dict);
  add_string pps " : ";  
  add_string pps "("; 
  pptff_term pps term dict pflag;
  add_string pps ")" 
  )
and pptff_app pps str argl dict pflag =
  (
  add_string pps str;
  add_string pps "(";
  pptff_argl pps argl dict pflag; 
  add_string pps ")"
  )  


(* END PRINT_TERM *)


(* PRINT_TFF *)
(* useful functions *)
fun nl2 pps = (add_newline pps; add_newline pps) 
fun indent4 pps = ((* to be replaced with begin block maybe *)
                    add_newline pps; 
                    add_string pps (space 4)
)

fun pptff_commentline pps =
  (add_string pps 
"%------------------------------------------------------------------------------"
  ; nl2 pps )

fun has_simplety ((ty,arity),name) = (arity = 0)
fun get_simpletyadict tyadict = filter has_simplety tyadict

fun is_dtyname name = (substring (name,0,1) = "$")
fun is_not_dtyname name = not (is_dtyname name)
fun has_not_dtyname ((ty,arity),name) = is_not_dtyname name  
fun erase_dtyname tyadict = filter has_not_dtyname tyadict

(* end useful functions *)

(* type *)
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
    
  (* print the type of free variables or constant *)  
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


(* axiom *)
fun pptff_axiom pps name term dict =
  ( 
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  pptff_term pps term dict true;
  add_string pps " ))."
  ) 

fun pptff_axioml_aux pps terml dict start =
  case terml of
    [] => ()
  | t :: m =>  
    (
    pptff_axiom pps ("axiom" ^ (Int.toString start)) t dict;
    nl2 pps;
    pptff_axioml_aux pps m dict (start + 1)
    )

fun pptff_axioml pps terml dict = pptff_axioml_aux pps terml dict 1;      
    
fun pptff_conjecture pps name term dict =
  if term = F then ()
  else
    ( 
    add_string pps ("tff(" ^ name ^ "_conjecture,conjecture,(");
    indent4 pps;
    pptff_term pps term dict true;
    add_string pps " )).";
    nl2 pps
    )     
  
(* should do something so that the user 
knows all the transformation done to his formula *)
fun pptff_btrue_bfalse pps =
  (
  pptff_type pps "btrue" "bool";
  nl2 pps;
  pptff_type pps "bfalse" "bool";
  nl2 pps 
  )


fun pptff_tff pps goal =
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
    if firstorder term
    then 
      let 
      (* dict *)
        val tyadict = create_tyadict term
        val simpletyadict = erase_dtyname (get_simpletyadict tyadict)
        val bvdict = create_bvdict term  
        val bvatydict = create_bvatydict term tyadict (* not used in printterm *)
        val fvdict = create_fvdict term 
        val fvatydict = create_fvatydict term tyadict
        val cdict = create_cdict term 
        val catydict = create_catydict term tyadict
      in
      let val dict = (tyadict,bvdict,fvdict,cdict) in
      (
      begin_block pps CONSISTENT 0;
        pptff_commentline pps;
        pptff_tyadict pps simpletyadict;
        pptff_fvatydict pps fvdict fvatydict;
        pptff_catydict pps cdict catydict;
        if has_boolarg term then pptff_btrue_bfalse pps else ();
        pptff_axioml pps (fst goal) dict;
        pptff_conjecture pps "conjecture" (snd goal) dict;
        pptff_commentline pps;
        nl2 pps;
      end_block pps
      )
      end end
    else
      raise PRINTTFF_ERR "pptff_tff" ((term_to_string term) ^ " :higher order")
  end end end 

(* OUTPUT TFF *)
fun output_tffgoal path goal appendflag =
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
    pptff_tff pps goal;
    TextIO.closeOut file
    )  
  end end
  
(* test
val thm = ;
val path = ;
*)


end



