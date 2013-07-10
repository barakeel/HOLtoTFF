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
open HOLPP; open numSyntax;
*)
open HolKernel HOLPP numSyntax 
     stringtools listtools mydatatype
     extractvar extracttype namevar nametype higherorder

(* not all structures are necessary *)

fun PRINTTFF_ERR function message =
    HOL_ERR{origin_structure = "printtff",
            origin_function = function,
            message = message}

(*PRINT_TERM*)
fun print_bvl_aux pps bvl bvdict tyadict  =
  case bvl of
    [] => raise PRINTTFF_ERR "print_bvl_aux" "emptylist"
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
               print_bvl_aux pps m bvdict tyadict
               )  

fun print_bvl pps bvl bvdict tyadict = 
  (
  add_string pps "[";
  print_bvl_aux pps bvl bvdict tyadict;
  add_string pps "]"
  )



(* not sure on the result if there is nested quantification *)
(* an injective mapping only if term is in cnf  *)

(* only for first order *)
(* 
#1 dict : list of ((type,arity), its name) 
#2 dict : list of (bound variable, its name) 
#3 dict : list of (free variable, its name)  
#4 dict : list of (constant, its name) 
*)


(* defined operators should have the right number of arguments *)
(* pflag : predicateflag *)

(* dict isn't modified by print_term *)
fun print_term pps term dict pflag =
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
      Conj => print_binop pps "&" term dict pflag
    | Disj => print_binop pps "|" term dict pflag
    | Neg => print_unop pps "~" term dict pflag 
    | Imp_only => print_binop pps "=>" term dict pflag
    | Forall => let val (qbvl,t) = strip_forall term in
                          print_quant pps "!" qbvl t dict pflag
                        end       
    | Exists => let val (qbvl,t) = strip_exists term in
                          print_quant pps "?" qbvl t dict pflag
                        end
    | App => 
      let val (operator,argl) = strip_comb term in
      case termstructure operator of
        Numeral => raise PRINTTFF_ERR "print_term" "numeral"
      | Var => if is_member term (map fst (#2 dict))
               then print_app pps (lookup operator (#2 dict)) argl dict false
               else print_app pps (lookup operator (#3 dict)) argl dict false 
      | Const => 
        (
        case nodeconst term of
          Eq => if pflag andalso 
                   (
                   case termstructure (lhs term) of
                     Numeral => false
                   | Var => lookup (lhs term) fvatydict = "$o"
                   | Const => lookup (lhs term) catydict = "$o"
                   | Comb => 
                     if is_logical (lhs term)
                     then true
                     else 
                       let val (operator,argl) = strip_comb (lhs term) in
                       case termstructure operator of
                         Numeral => raise PRINTTFF_ERR "print_term" "numeral"
                       | Var => last2str (lookup (lhs term) fvatydict) = "$o" 
                       | Const => last2str (lookup (lhs term) catydict) = "$o"           
                       | _ => raise PRINTTFF_ERR "print_term" "abs or comb"      
                       end       
                   
                   
                   
                   
                   
                   
                   | Abs => raise PRINTTFF_ERR "print_term" "abs"
                   fvctyadict
                   lookup (type_of (lhs term),0) = "$o" tydict andalso 
                   lookup (type_of (rhs term),0) = "$o" tydict
                then print_binop pps "<=>" term dict pflag
                else print_binop pps "=" term dict false
        | Add => print_app pps "$sum" argl dict false
        | Minus => print_app pps "$difference" argl dict false 
        | Mult => print_app pps "$product" argl dict false  
        | Less => print_app pps "$less" argl dict false  
        | Greater => print_app pps "$greater" argl dict false  
        | Geq => print_app pps "$greatereq" argl dict false  
        | Leq => print_app pps "$lesseq" argl dict false
        | Newnodeconst => print_app pps 
                          (lookup operator (#4 dict)) argl dict false
        ) 
      | _ => raise PRINTTFF_ERR "print_term" "abs or comb"
      end
      
    )
  | Abs => raise PRINTTFF_ERR "print_term" "abs"
and print_argl pps argl dict pflag = 
  case argl of
    [] => raise PRINTTFF_ERR "print_argl" "emptylist"
  | [arg] => print_term pps arg dict pflag
  | arg :: m => 
    ( 
    print_term pps arg dict pflag; 
    add_string pps ",";
    print_argl pps m dict pflag
    ) 
and print_unop pps str term dict pflag =
  (
  add_string pps ("( " ^ str ^ " ");
  print_term pps (rand term) dict pflag;
  add_string pps " )"
  )
and print_binop pps str term dict pflag = 
  (
  add_string pps "( ";
  print_term pps (lhand term) dict pflag;
  add_string pps (" " ^ str ^ " ");
  print_term pps (rand term) dict pflag;
  add_string pps " )"
  )
and print_quant pps str bvl term dict pflag = 
  (
  add_string pps (str ^ " ");
  print_bvl pps bvl (#2 dict) (#1 dict);
  add_string pps " : ";  
  add_string pps "( "; 
  print_term pps term dict pflag;
  add_string pps " )" 
  )
and print_app pps str argl dict pflag =
  (
  add_string pps str;
  add_string pps "(";
  print_argl pps argl dict pflag; 
  add_string pps ")"
  )  


(* END PRINT_TERM *)

(* PRINT_THM *)
(* useful functions *)
fun nl2 pps = (add_newline pps; add_newline pps) 
fun indent4 pps = ((* to be replaced with begin block maybe *)
                    add_newline pps; 
                    add_string pps (space 4)
)

fun has_simplety ((ty,arity),name) = (arity = 0)
fun get_simpletyadict tyadict = filter has_simplety tyadict

fun is_dtyname name = (substring (name,0,1) = "$")
fun is_not_dtyname name = not (is_dtyname name)
fun has_not_dtyname ((ty,arity),name) = is_not_dtyname name  
fun erase_dtyname tyadict = filter has_not_dtyname tyadict
(* end useful functions *)

(* type *)
fun print_type pps name tyname =
  ( 
  add_string pps ("tff(" ^ name ^ "_type,type,(");
  indent4 pps;
  add_string pps (name ^ ": " ^ tyname ^ " )).")
  ) 
  (* argument should only be the simpletyadict *)
fun print_tyadict pps tyadict =
   case tyadict of
    [] => ()
  | ((ty,a),name) :: m => 
    (
    print_type pps name "$tType";
    nl2 pps;
    print_tyadict pps m
    )
    
  (* print the type of free variables or constant *)  
fun print_fvatydict pps fvdict fvatydict =
  case fvatydict of
    [] => () 
  | ((fv,arity),tyname) :: m => 
    (
    print_type pps (lookup fv fvdict) tyname;
    nl2 pps;
    print_fvatydict pps fvdict m
    )

fun print_catydict pps cdict catydict =
  case catydict of
    [] => () 
  | ((c,arity),tyname) :: m => 
    (
    print_type pps (lookup c cdict) tyname;
    nl2 pps;
    print_catydict pps cdict m
    )


(* axiom *)
fun print_axiom pps name term dict =
  ( 
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  print_term pps term dict true;
  add_string pps " ))."
  ) 

fun print_axioml_aux pps terml dict start =
  case terml of
    [] => ()
  | t :: m =>  
    (
    print_axiom pps ("axiom" ^ (Int.toString start)) t dict;
    nl2 pps;
    print_axioml_aux pps m dict (start + 1)
    )

fun print_axioml pps terml dict = print_axioml_aux pps terml dict 1;      
    
fun print_conjecture pps name term dict =
  if term = F then ()
  else
    ( 
    add_string pps ("tff(" ^ name ^ "_conjecture,conjecture,(");
    indent4 pps;
    print_term pps term dict true;
    add_string pps " ))."
    )     
  


(* should do something so that the user 
knows all the transformation done to his formula *)

(* PRINT_THM *)
fun print_thm pps thm =
  let val hypl = hyp thm in
  let val goal = concl thm in
  let val terml = hypl @ [goal] in
  let val term = list_mk_conj (terml) in 
  (* this term is only there to extract variables from *)
  let 
    (* free variables or constant *)
    val fval = collapse_lowestarity (get_fval (extract_var term)) 
    val cal = collapse_lowestarity (get_cal (extract_var term)) 
    (* dict *)
    val tyadict = create_tyadict term
    val simpletyadict = erase_dtyname (get_simpletyadict tyadict)
    val bvdict = create_bvdict term  
    val fvdict = create_fvdict term 
    val fvatydict = create_fvatydict term tyadict
    val cdict = create_cdict term 
    val catydict = create_catydict term tyadict
  in
  let val dict = (tyadict,bvdict,fvdict,cdict) in
  (* if firstorder term
  then *)
    (
    begin_block pps CONSISTENT 0;
      print_tyadict pps simpletyadict;
      print_fvatydict pps fvdict fvatydict;
      print_catydict pps cdict catydict;
      print_axioml pps hypl dict;
      print_conjecture pps "conjecture" goal dict;
    end_block pps
    )
  (* else
    raise PRINTTFF_ERR "print_thm" "higher order" *)
  end end end end end
  end
  
(* test
val thm = th3;
print_thm th3; *)
    
(* need the full path of your file (eg /home/problem.p) *)
fun output_tff path thm =
  let val file = TextIO.openOut path in 
  let val pps = PP.mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 80,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in 
    (
    print_thm pps thm;
    TextIO.closeOut file
    )  
  end end
  



end



