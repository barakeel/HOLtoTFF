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
fun print_bvl2 pps bvl bvdict tyadict  =
  case bvl of
    [] => raise PRINTTFF_ERR "print_bvl2" "emptylist"
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
               print_bvl2 pps m bvdict tyadict
               )  

fun print_bvl pps bvl bvdict tyadict = 
  (
  add_string pps "[";
  print_bvl2 pps bvl bvdict tyadict;
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

(* dict isn't modify by print_term *)
fun print_term pps term dict =
  case termstructure term of
    Numeral => add_string pps (name_numeral term)
  | Var => if is_member term (map fst (#2 dict))
           then add_string pps (lookup term (#2 dict)) (*boundvar*)
           else add_string pps (lookup term (#3 dict)) (*freevar*)
  | Const => add_string pps (lookup term (#4 dict))
  | Comb => 
    (
    case connective term of  
      Conj => print_binop pps "&" term dict
    | Disj => print_binop pps "|" term dict
    | Neg => print_unop pps "~" term dict 
    | Imp_only => print_binop pps "=>" term dict
    | Forall => let val (qbvl,t) = strip_forall term in
                          print_quant pps "!" qbvl t dict
                        end       
    | Exists => let val (qbvl,t) = strip_exists term in
                          print_quant pps "?" qbvl t dict
                        end
    | App => 
      let val (operator,argl) = strip_comb term in
      case termstructure operator of
        Numeral => raise PRINTTFF_ERR "print_term" "operator is numeral"
      | Var => if is_member term (map fst (#2 dict))
               then print_app pps (lookup term (#2 dict)) argl dict 
               else print_app pps (lookup term (#3 dict)) argl dict 
      | Const => 
        (
        case nodefvc term of
          Eq => print_binop pps "=" term dict
        | Add => print_app pps "$sum" argl dict
        | Minus => print_app pps "$difference" argl dict  
        | Mult => print_app pps "$product" argl dict  
        | Less => print_app pps "$less" argl dict  
        | Greater => print_app pps "$greater" argl dict  
        | Geq => print_app pps "$greatereq" argl dict  
        | Leq => print_app pps "$lesseq" argl dict
        | Newnodefvc => print_app pps (lookup operator (#4 dict)) argl dict      
        ) 
      | Comb => raise PRINTTFF_ERR "print_term" "operator is comb"
      | Abs => raise PRINTTFF_ERR "print_term" "abstraction"
      end
      
    )
  | Abs => raise PRINTTFF_ERR "print_term" "abstraction"
and print_argl pps argl dict = 
  case argl of
    [] => raise PRINTTFF_ERR "print_argl" "emptylist"
  | [arg] => print_term pps arg dict
  | arg :: m => ( 
              print_term pps arg dict; 
              add_string pps ",";
              print_argl pps m dict
              ) 
and print_unop pps str term dict =
  let val (operator,l) = strip_comb term in
  let val lhs =  hd l in
    (
    add_string pps ("( " ^ str ^ " ");
    print_term pps lhs dict;
    add_string pps " )"
    )
  end end
and print_binop pps str term dict = 
  let val (operator,l) = strip_comb term in
  let 
    val lhs = hd l
    val rhs = hd (tl l) 
  in   
    (
    add_string pps "( ";
    print_term pps lhs dict;
    add_string pps (" " ^ str ^ " ");
    print_term pps rhs dict;
    add_string pps " )"
    )
  end end
and print_quant pps str bvl term dict = 
  (
  add_string pps (str ^ " ");
  print_bvl pps bvl (#2 dict) (#1 dict);
  add_string pps " : ";  
  add_string pps "( "; 
  print_term pps term dict;
  add_string pps " )" 
  )
and print_app pps str argl dict =
  (
  add_string pps str;
  add_string pps "(";
  print_argl pps argl dict; 
  add_string pps ")"
  )  
(* END PRINT_TERM *)

(* PRINT_PB *)
(* useful functions *)
fun nl2 pps = (
                add_newline pps;
                add_newline pps
                ) 
fun indent4 pps = ((* to be replaced with begin block maybe *)
                    add_newline pps; 
                    add_string pps (space 4)
)

fun is_in_simpletyadict ((ty,arity),name) = (arity = 0)

fun get_simpletyadict tyadict = filter is_in_simpletyadict tyadict
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
fun print_fvctyl pps fvcal fvcdict tyadict =
  case fvcal of
    [] => () 
  | (fvc,arity) :: m => 
    let val name = lookup fvc fvcdict in
    let val tyname = lookup (type_of fvc,arity) tyadict in 
      (
      print_type pps name tyname;
      nl2 pps;
      print_fvctyl pps m fvcdict tyadict
      )
    end end

(* axiom *)
fun print_axiom pps name term dict =
  ( 
  add_string pps ("tff(" ^ name ^ "_axiom,axiom,(");
  indent4 pps;
  print_term pps term dict;
  add_string pps " ))."
  ) 

(* main function *)
fun print_pb pps term = 
  let 
    (* free variables or constant *)
    val fval = collapse_lowestarity (get_fval (extract_var term)) 
    val cal = collapse_lowestarity (get_cal (extract_var term)) 
    (* dict *)
    val tyadict = create_tyadict term
    val simpletyadict = get_simpletyadict tyadict
    val bvdict = create_bvdict term  
    val fvdict = create_fvdict term 
    val cdict = create_cdict term 
  in
  let val dict = (tyadict,bvdict,fvdict,cdict) in
    
  (* if firstorder term
  then *)
    (
    begin_block pps CONSISTENT 0;
      print_tyadict pps simpletyadict;
      print_fvctyl pps fval fvdict tyadict;
      print_fvctyl pps cal cdict tyadict;
      print_axiom pps "axiom" term dict;
    end_block pps
    )
  (* else
    raise PRINTTFF_ERR "print_thm" "higher order" *)
  end end

(* END PRINT_PB *)

(* should do something so that the user 
knows all the transformation done to his formula *)


(* need the full path of your file (eg /home/problem.p) *)
fun output_tff path term =
  let val file = TextIO.openOut path in 
  let val pps = PP.mk_ppstream 
                  {
                  consumer  = fn s => TextIO.output (file,s),
                  linewidth = 80,
                  flush  = fn () => TextIO.flushOut file
                  } 
  in 
    (
    print_pb pps term;
    TextIO.closeOut file
    )  
  end end
  



end



