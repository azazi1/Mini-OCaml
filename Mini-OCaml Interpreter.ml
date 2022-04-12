(* Project Mini-OCaml Interpreter: Aiman Al-Azazi, 20.12.2021 *)

(* 1: Lexer *)

(* Token Type Declarations *)
type const   = BCON of bool | ICON of int
type token   = LP | RP | EQ | COL | ARR 
             | ADD | SUB | MUL | LEQ
             | IF | THEN | ELSE 
             | LAM | LET | IN | REC
             | CON of const | VAR of string 
             | BOOL | INT

(* Auxiliary  Functions for lexer *)             
let code = Char.code
let num c = code c - code '0'
let digit c = code '0' <= code c && code c <= code '9'
let lc_letter c = code 'a' <= code c && code c <= code 'z'
let uc_letter c = code 'A' <= code c && code c <= code 'Z'
let whitespace c = match c with
  | ' ' | '\n' |  '\t' | '\r' -> true
  | _ -> false 
(* Note: I added '\r' in whitespace function in order to skip  \n\r  *)

(* Main Lexer Function *)
let lex s : token list =
  let get i = String.get s i in
  let getstr i n = String.sub s (i-n) n in
  let exhausted i = i >= String.length s in
  let verify i c = not (exhausted i) && get i = c in
  let rec lex i l =
    if exhausted i then List.rev l
    else match get i with
      | '+' -> lex (i+1) (ADD::l)
      | '*' -> lex (i+1) (MUL::l)
      | '=' -> lex (i+1) (EQ::l)
      | '(' -> lex (i+1) (LP::l)
      | ')' -> lex (i+1) (RP::l)
      | ':' -> lex (i+1) (COL::l)
      | '<' -> if verify (i+1) '='
          then lex (i+2) (LEQ::l)
          else failwith "1.1 lex: '=' expected"
      | '-' -> if verify (i+1) '>'
          then lex (i+2) (ARR::l)
          else lex (i+1) (SUB::l)
      | c when whitespace c -> lex (i+1) l
      | c when digit c -> lex_num (i+1) (num c) l
      | c when lc_letter c -> lex_id (i+1) 1 l
      | c -> failwith "1.2 lex: illegal character"
  and lex_num i n l =
    if exhausted i then lex_num' i n l
    else let c = get i in
      if digit c then lex_num (i+1) (10*n + num c) l
      else lex_num' i n l
  and lex_num' i n l = lex i (CON (ICON n)::l)
  and lex_id i n l =
    if exhausted i then lex_id' i n l
    else match get i with
      | '\'' | '_' -> lex_id (i+1) (n+1) l
      | c -> if lc_letter c || uc_letter c || digit c
          then lex_id (i+1) (n+1) l
          else lex_id' i n l
  and lex_id' i n l = match getstr i n with
    | "if" -> lex i (IF::l)
    | "then" -> lex i (THEN::l)
    | "else" -> lex i (ELSE::l)
    | "fun" -> lex i (LAM::l)
    | "let" -> lex i (LET::l)
    | "in" -> lex i (IN::l)
    | "rec" -> lex i (REC::l)
    | "false" -> lex i (CON (BCON false)::l)
    | "true" -> lex i (CON (BCON true)::l)
    | "int" -> lex i (INT::l)
    | "bool" -> lex i (BOOL::l)
    | s -> lex i (VAR s::l)
  in lex 0 []

(* Testing Lexer *)    
let fac_string =
  "let rec fac (a:int) :int -> int = 
       fun (n:int) -> if n <= 1 then a else fac (n*a) (n-1) in fac 1 5"
let prod_string = "let x = 3 * 3*3 in x"

let test_lex1 = lex fac_string
let test_lex2 = lex prod_string   
(* ___________________________________________________________ *)

    
(* 2: Parser *) 

(* Expression Type Declarations *)
type ty  = Int | Bool | Arrow of ty * ty
type var = string
type con = Bcon of bool | Icon of int
type op  = Add | Sub | Mul | Leq
type exp = Var of var | Con of con
         | Oapp of op * exp * exp
         | Fapp of exp * exp
         | If of exp * exp * exp
         | Lam of var * exp
         | Lamty of var * ty * exp
         | Let of var * exp * exp
         | Letrec of var * var * exp * exp
         | Letrecty of var * var * ty * ty * exp * exp

(* Auxiliary  Functions for Parser *)                       
let verify c l =  match l with
  | [] -> failwith "2.1 verify: no token"
  | c'::l -> if c'=c then l else failwith "verify: wrong token"
           
let checkParse (result ,l) =
  if l = [] then result
  else failwith "2.2 checkParse : to many tokens "
      
(* Type Parser *)      
let rec ty l = let (t,l) = pty l in ty' t l
and  ty' t l = match l with
  | ARR::l -> 
      let (t',l) = pty l in
      let (t'',l) = ty' t' l in
      (Arrow (t, t''), l)
  | _ -> (t,l) 
and pty l = match l with
  | INT::l -> (Int, l)
  | BOOL::l -> (Bool, l)
  | LP::l -> let (t,l) = ty l in (t, verify RP l)
  | _ -> failwith "2.3 ty: type expected"
           
(* Main Parser Function *)
let exp l' =
  let rec exp l : exp * token list = match l with
    | IF::l ->
        let (e1,l) = exp l in
        let (e2,l) = exp (verify THEN l) in
        let (e3,l) = exp (verify ELSE l) in
        (If(e1,e2,e3), l)
    | LAM::VAR x::ARR::l ->
        let (e,l) = exp l in (Lam (x,e), l)
    | LAM::LP::VAR x::COL::l ->
        let (t,l) = ty l in
        let (e,l) = exp (verify ARR (verify RP l)) in
        (Lamty (x,t,e), l)
    | LET::VAR x::EQ::l ->
        let (e1,l) = exp l in
        let (e2,l) = exp (verify IN l) in
        (Let (x,e1,e2), l)
    | LET::REC::VAR f::VAR x::EQ::l ->
        let (e1,l) = exp l in
        let (e2,l) = exp (verify IN l) in
        (Letrec (f,x,e1,e2), l)
    | LET::REC::VAR f::LP::VAR x::COL::l -> 
        let (t1,l) = ty l in
        let (t2,l) = ty (verify COL (verify RP l)) in
        let (e1,l) = exp (verify EQ l) in
        let (e2,l) = exp (verify IN l) in
        (Letrecty (f,x,t1,t2,e1,e2), l)
    | l -> cexp l
  and cexp l = let (e,l) = sexp l in cexp' e l
  and cexp' e1 l = match l with
    | LEQ::l -> let (e2,l) = sexp l in (Oapp(Leq,e1,e2), l)
    | l -> (e1,l)
  and sexp l = let (e,l) = mexp l in sexp' e l
  and sexp' e1 l = match l with
    | ADD::l -> let (e2,l) = mexp l in sexp' (Oapp(Add,e1,e2)) l
    | SUB::l -> let (e2,l) = mexp l in sexp' (Oapp(Sub,e1,e2)) l
    | l -> (e1,l)
  and mexp l = let (e,l) = aexp l in mexp' e l
  and mexp' e1 l = match l with
    | MUL::l -> let (e2,l) = aexp l in mexp' (Oapp(Mul,e1,e2)) l
    | l -> (e1,l)
  and aexp l = let (e,l) = pexp l in aexp' e l
  and aexp' e1 l = match l with
    | CON _ :: _ | VAR _ :: _ | LP :: _  ->
        let (e2,l) = pexp l in aexp' (Fapp(e1,e2)) l
    | l -> (e1,l)
  and pexp l = match l with
    | CON (BCON b)::l -> (Con (Bcon b), l)
    | CON (ICON n)::l -> (Con (Icon n), l)
    | VAR x::l -> (Var x, l)
    | LP::l -> let (e,l) = exp l in (e, verify RP l)
    |  _ -> failwith "2.4 pexp: parser error"
  in checkParse (exp l')

(* testing parser *)    
let test_par1 = exp (lex fac_string)
let test_par2 = exp (lex prod_string)
    
(* ___________________________________________________________ *)    
 

(* 3: Type Checker *) 

(* Environment Type Declaration *)
type ('a,'b) env = ('a * 'b) list
    
(* Auxiliary  Functions for Type Checker *)     
let empty : ('a,'b) env = []
let update (env : ('a,'b) env) a b : ('a,'b) env = (a,b) :: env
let rec lookup (env : ('a,'b) env) a =  match env with
  | (a',b) :: env -> if a = a' then Some b else lookup env a
  | [] -> None
               
(* helper function for operator application *)   
let check_op o t1 t2 : ty = match o, t1, t2 with
  | Add, Int, Int -> Int
  | Sub, Int, Int -> Int
  | Mul, Int, Int -> Int
  | Leq, Int, Int -> Bool
  | _, _ , _ -> failwith "3.1 op app: ill-typed arguments"

(* helper functions for function application *)                  
let check_fun t1 t2 : ty = match t1 with
  | Arrow (t11,t12) -> if t11 = t2 then t12
      else failwith "3.2 fun app: wrong argument type"
  | _ -> failwith "3.3 fun app: function expected"

(* Main Type Checker Function *)               
let rec check env e : ty = match e with
  | Var x ->
      begin match lookup env x with
        | Some t -> t
        | None -> failwith ("3.4 var: variable"^x^"unbound")
      end
  | Con (Bcon b) -> Bool
  | Con (Icon n) -> Int
  | Oapp (o,e1,e2) -> check_op o (check env e1) (check env e2)
  | Fapp (e1,e2) -> check_fun (check env e1) (check env e2)
  | If (e1,e2,e3) ->
      begin match check env e1, check env e2, check env e3 with
        | Bool, t2, t3 -> if t2 = t3 then t2
            else failwith "3.5 if: then and else type not equal"
        | _, _, _  -> failwith "3.6 if: bool expected"
      end
  | Lam (_,_) -> failwith "3.7 fun: missing type"
  | Lamty (x,t,e) -> Arrow (t, check (update env x t) e)
  | Let (x,e1,e2) -> check (update env x (check env e1)) e2
  | Letrec (_,_,_,_) -> failwith "3.8 let rec: missing types"
  | Letrecty (f,x,t1,t2,e1,e2) ->
      let env1 = update env f (Arrow(t1,t2)) in
      if check (update env1 x t1) e1 = t2 then check env1 e2
      else failwith "3.9 let rec: declared type not matched"

(* testing type checker *)          
let test_typ1 = check empty (exp (lex fac_string))
let test_typ2 = check empty (exp (lex prod_string))
    
(* ___________________________________________________________ *)     
 

(* 4: Evaluator *)

(* Value Type Declaration *)
type value = Bval of bool | Ival of int
           | Closure of var * exp * (var, value) env
           | Rclosure of var * var * exp * (var, value) env

(* helper function for operator application *)                           
let eval_op o v1 v2 = match o, v1, v2 with
  | Add, Ival n1, Ival n2 -> Ival (n1 + n2)
  | Sub, Ival n1, Ival n2 -> Ival (n1 - n2)
  | Mul, Ival n1, Ival n2 -> Ival (n1 * n2)
  | Leq, Ival n1, Ival n2 -> Bval (n1 <= n2)
  | _, _ , _ -> failwith "4.1 op app: ill-typed arguments"

(* Main Type Checker Function 
(Matually Recussive with an Helper Evalutor for Function Application) *)                                                  
let rec eval env e : value = match e with
  | Var x ->
      begin match lookup env x with
        | Some v -> v
        | None -> failwith ("4.2 var: variable"^x^"unbound")
      end
  | Con (Bcon b) -> Bval b
  | Con (Icon n) -> Ival n
  | Oapp (o,e1,e2) -> eval_op o (eval env e1) (eval env e2)
  | Fapp (e1,e2) -> eval_fun (eval env e1) (eval env e2)
  | If (e1,e2,e3) ->
      begin match eval env e1 with
        | Bval b -> eval env (if b then e2 else e3)
        | _ -> failwith "4.3 if: boolean expected"
      end
  | Lam (x,e) | Lamty (x,_,e) -> Closure (x,e,env)
  | Let (x,e1,e2) -> eval (update env x (eval env e1)) e2
  | Letrec (f,x,e1,e2) | Letrecty (f,x,_,_,e1,e2) -> 
      eval (update env f (Rclosure (f,x,e1,env))) e2
and eval_fun v1 v2 = match v1 with
  | Closure (x,e,env) -> eval (update env x v2) e
  | Rclosure (f,x,e,env) -> eval (update (update env f v1) x v2) e
  | _ -> failwith "4.4 fun app: function expected"

(* testing evaluator *)          
let test_eval1 = eval empty (exp (lex fac_string))           
let test_eval2 = eval empty (exp (lex prod_string))
    
(* ___________________________________________________________ *)     