(* ABSTRACT SYNTAX *)

type VALUE = INT of int

type BINOP = BPLUS | BMINUS | BTIMES

type RANGEOP = RSUM | RPROD | RMAX | RARGMAX

type EXP =
  | CONSTANT  of VALUE
  | VARIABLE  of string
  | OPERATE   of BINOP * EXP * EXP
  | LET_IN    of string * EXP * EXP
  | OVER      of RANGEOP * string * EXP * EXP * EXP

(* A list mapping variable names to their values. *)
type SymTab = (string * VALUE) list

(* Inserts a variable into the variable table. *)
let bind v k vtab = (v, k) :: vtab : SymTab

(* Lookup the value of a variable. *)
let rec lookup v = function
  | (v', k) :: vtab -> if v = v' then k else lookup v vtab
  | (_ : SymTab)    -> failwith ("unbound variable : " + v)

(* EVALUATION *)

(*****************************************************
 * TODO: Task 2: complete the definition of `eval`. You may also
 * define any auxiliary functions as you see fit, to help express `eval`
 * as cleanly and concisely as possible.
 ****************************************************)

(* Function that evaluates a binary operation *)
let binop op n1 n2 =
  match op with
    | BPLUS  -> INT (n1 + n2)
    | BMINUS -> INT (n1 - n2)
    | BTIMES -> INT (n1 * n2)

(* The evaluation function. *)
let rec eval (vtab : SymTab) (e : EXP) : VALUE =
  match e with
    | CONSTANT n -> n

    | VARIABLE v -> lookup v vtab

    | OPERATE (op, e1, e2) -> 
      match (eval vtab e1, eval vtab e2) with
        | (INT n1, INT n2) -> binop op n1 n2

    | LET_IN (var, e1, e2) -> 
      let n1 = eval vtab e1
      let vtab1 = bind var n1 vtab
      eval vtab1 e2

    | OVER (rop, var, e1, e2, e3) -> 
      let n1 = eval vtab e1
      let n2 = eval vtab e2
      match rop with
        | RSUM | RPROD ->
          let (operator, init) = 
            match rop with
              | RSUM -> ((+), 0)
              | _ -> ((*), 1)  // since it has to be RSUM or RPROD to enter this branch, the wildcarn pattern will always match RPROD
          if n1 > n2 then INT init
          else
            let rec sum x acc =
              if x > n2 then acc
              else
                let vtab1 = bind var x vtab
                sum (match x with INT x -> INT (x+1)) (match((eval vtab1 e3), acc) with (INT r, INT acc) -> INT (operator r acc))
            sum n1 (INT init)

        | RMAX ->
          let n1 = eval vtab e1
          let n2 = eval vtab e2
          if n1 > n2 then failwith "upper bound on the range must be greater or equal to the lower bound"
          else
            let rec max x currentMax =
              if x > n2 then currentMax
              else
                let vtab1 = bind var x vtab
                let newMax = 
                  match ((eval vtab1 e3), currentMax) with
                    | (INT r, INT cMax) -> if r > cMax then INT r else INT cMax
                max (match x with INT x -> INT (x+1)) newMax
            max n1 (INT -2147483648)

        | RARGMAX -> // TODO: rewrite function such that 
          let n1 = eval vtab e1
          let n2 = eval vtab e2
          if n1 > n2 then failwith "upper bound on the range must be greater or equal to the lower bound"
          else 
            let rec argmax x max maxIndex =      // x = current num, max = max thus far, index = current index, maxIndex = maxIndex
              if x > n2 then INT maxIndex
              else
                let index =
                  match (x, n1) with (INT x, INT n1) -> x-n1
                let vtab1 = bind var x vtab
                let (newMax, newMaxIndex) =
                  match ((eval vtab1 e3), max) with
                    | (INT r, INT cMax) -> if r > cMax then (INT r, index) else (INT cMax, maxIndex)
                argmax (match x with INT x -> INT (x+1)) newMax newMaxIndex
            argmax n1 (INT -2147483648) 0

(* YOU SHOULDN'T NEED TO MODIFY ANYTHING IN THE REMAINDER OF THIS FILE,
   BUT YOU ARE WELCOME TO LOOK AT IT. *)

(* LEXER
 **********
 * A lexer, is a program which reads a stream/list of chars,
 * and transforms them into a list of tokens.
 **********
 * This example code is very simple and naive, but it should not
 * introduce anything which you have not seen on the PoP course.
 * Furhter more, we hope that you will read it, and get an intuition
 * about what is going on
 **********
 *)

type TOKEN =
  | NUM of int | ID of string
  | PLUS | MULT | MINUS | EQ
  | LPAR | RPAR | LET  | IN
  | SUM | PROD | MAX | ARGMAX | OF | TO

let explode (s : string) = [for c in s -> c]
let isA t c = List.exists (fun c' -> c = c') t

let digit      = ['0'..'9']
let letter     = ['a'..'z']
let symbol     = explode "+-*/=()"
let whitespace = explode " \t\n"

let keyword    = ["let"; "in"; "sum"; "prod"; "max"; "argmax"; "of"; "to"]

let rec lex = function
  | (c ::  _) as cs when c |> isA digit      -> lexNum  "" cs
  | (c ::  _) as cs when c |> isA letter     -> lexWord "" cs
  | (c :: cs)       when c |> isA symbol     -> lexSymbol c :: lex cs
  | (c :: cs)       when c |> isA whitespace ->                lex cs
  | (c :: cs)       -> failwith ("invalid character : " + string c)
  | (_ : char list) -> ([] : TOKEN list)

and lexNum s = function
  | (c :: cs) when c |> isA digit -> lexNum (s + string c) cs
  |       cs                      -> (NUM (System.Int32.Parse s)) :: lex cs

and lexWord s = function
  | (c :: cs) when c |> isA (letter @ digit) -> lexWord (s + string c) cs
  |       cs                                 ->
    (if s |> isA keyword then getKeyWord s else ID s) :: lex cs

and lexSymbol = function
  | '+' -> PLUS
  | '-' -> MINUS
  | '*' -> MULT
  | '=' -> EQ
  | '(' -> LPAR
  | ')' -> RPAR
  | sym  -> failwith ("Unknown Symbol : " + string sym)

and getKeyWord = function
  | "let" -> LET
  | "in"  -> IN
  | "sum"  -> SUM
  | "prod"  -> PROD
  | "max"  -> MAX
  | "argmax"  -> ARGMAX
  | "to"  -> TO
  | "of"  -> OF
  | word  -> failwith ("Invalid Keyword : " + word)

(* PARSER
 **********
 * A parser transforms the list of tokens to an abstract syntax tree,
 * which reprecents the syntax of an expression.
 **********
 * The example code uses a somewhat ad hoc approach.
 * Later on in the course, we will see more systematic ways of
 * constructing parsers.
 *)


(* Returns tail of ts, assuming head of ts equals t *)
let expect t ts =
  match ts with
    | t' :: ts1 when t' = t -> ts1
    | _ -> failwith "parse error"

(* Each parser function returns the expression parsed from the beginning
   of the token list, together with any remaining tokens. *)

let rec parse_exp ts =
  match ts with
    | LET :: ID v :: EQ :: ts1 ->
       let (e1, ts2) = parse_exp ts1
       let ts3 = expect IN ts2
       let (e2, ts4) = parse_exp ts3
       (LET_IN (v,e1,e2), ts4)
    | r :: ID v :: EQ :: ts1  when r |> isA [SUM; PROD; MAX; ARGMAX] ->
       let (e1, ts2) = parse_exp ts1
       let ts3 = expect TO ts2
       let (e2, ts4) = parse_exp ts3
       let ts5 = expect OF ts4
       let (e3, ts6) = parse_exp ts5
       let rop = match r with
                  | SUM -> RSUM
                  | PROD -> RPROD
                  | MAX -> RMAX
                  | ARGMAX -> RARGMAX
                  | _ -> failwith ("Unknown range operation : " + string r)
       (OVER (rop, v, e1, e2, e3), ts6)
    | _ -> parse_arith ts

and parse_arith ts =
  let (e1, ts1) = parse_term ts
  parse_terms e1 ts1
and parse_terms e1 ts =
  match ts with
    | PLUS :: ts1 -> let (e2, ts2) = parse_term ts1
                     parse_terms (OPERATE (BPLUS, e1,e2)) ts2
    | MINUS :: ts1 -> let (e2, ts2) = parse_term ts1
                      parse_terms (OPERATE (BMINUS, e1,e2)) ts2
    | _ -> (e1, ts)

and parse_term ts =
  let (e1, ts1) = parse_factor ts
  parse_factors e1 ts1
and parse_factors e1 ts =
  match ts with
    | MULT :: ts1 -> let (e2, ts2) = parse_factor ts1
                     parse_factors (OPERATE (BTIMES, e1,e2)) ts2
    | _ -> (e1, ts)

and parse_factor ts =
  match ts with
    | ID v :: ts1 -> (VARIABLE v, ts1)
    | NUM n :: ts1 -> (CONSTANT (INT n), ts1)
    | LPAR :: ts1 ->
        let (e, ts2) = parse_exp ts1
        let ts3 = expect RPAR ts2
        (e, ts3)
    | _ -> failwith ("parse error")

let parse ts =
  let (e, ts1) = parse_exp ts
  if ts1 = [] then e else failwith "parse error"

(*************
 * When interpreting code, we lex it into tokens, parse the tokens into an
 * abstract syntax tree, and evaluate the tree into some value.
 * The definition of what it means to be a value, and an expression (tree),
 * can be found in the parser.
 *************
 * In this code, the evaluation of such a tree has been reprecented, should
 * be implemented in the below function [eval] {~_^}
 *)

(* FOR RUNNING A PROGRAM *)
let run program = (lex >> parse >> eval []) (explode program)

(* Tests *)
let eval_test_constant = (eval []             (CONSTANT (INT 4)) = INT 4)
let eval_test_lookup   = (eval [("x", INT 4)] (VARIABLE "x")     = INT 4)

let program0 = "1 - 2 - 3"
let program1 = "let x = 4 in x + 3"
let program2 = ("let x0 = 2 in \
                 let x1 = x0 * x0 in \
                 let x2 = x1 * x1 in x2 * x2")
let program3 = "sum x = 1 to 4 of x*x"
let program4 = "max x = 0 to 10 of 5 * x - x * x"
let program5 = "argmax x = 0 to 10 of 5 * x - x * x"

let eval_test_arithmetic = (run program0 = INT -4)
let eval_test_let        = (run program1 = INT 7)
let eval_test_nested_let = (run program2 = INT 256)
let eval_test_sum        = (run program3 = INT 30)
(*let eval_test_max        = (run program4 = INT 6)
let eval_test_argmax     = (run program4 = INT 2)
*)
printfn "test results:"
printfn "  eval_test_constant = %b" eval_test_constant
printfn "  eval_test_lookup = %b" eval_test_lookup
printfn "  eval_test_arithmetic = %b" eval_test_arithmetic
printfn "  eval_test_let = %b" eval_test_let
printfn "  eval_test_nested_let = %b" eval_test_nested_let

(* THIS FUNCTION CALLS RUN ON USER INPUT IN AN INTERACTIVE LOOP *)
let interpreter () =
  let mutable running = true
  printfn  "Welcome to the calculator! Type \"exit\" to stop."
  while running do
    printf  "Input an expression : "
    let program = System.Console.ReadLine()
    try
      if program = "" then ()
      else if program = "exit" then running <- false
      else printfn "Evaluation result   : %A" (run program)
    with
      | Failure (msg) -> printfn "%s" msg

interpreter ()
