open Batteries

type typ = 
| Bool
| TypeInt
| TypeFloat
| Fun of typ * typ 
| TypePair
| TypeVar

type pattern = 
| TrueP
| FalseP
| VarP of string * typ
| PairP of pattern * pattern

type id = Ident of string

type expression = 
| True 
| False
| Var of string 
| Int of int
| Float of float
| Lambda of string * typ * expression 
| App of expression * expression 
| If of expression * expression * expression 
| Match of expression * (pattern * expression) list
| Add of expression * expression
| Mult of expression * expression
| IsZero of expression
| Pair of expression * expression
| Fst of expression
| Snd of expression
| AddFloat of expression * expression
| MultFloat of expression * expression
| Ref of expression
| DeRef of expression
| Id of string
| Some of expression
| None
| Let of id * expression * expression
| Error

type label = Lab of string

(* Memory  *)
type memory = (string * expression) list

(* type store = Store.store

module type STORE = *)

(* let operators *)
let ( let* ) o f =
	match o with
	| None -> None
	| Some(x) -> f x

let return x = Some x

(* substitution *)
let rec substitution e v x = 
	match e with 
	| Var varname -> if varname = x then v else Var varname
	| True -> True
	| False -> False
	| Int(v) -> Int(v)
	| Float(v) -> Float(v)
	| Lambda(varname, typ, exp') -> if varname = x then Lambda(varname, typ, exp') else Lambda(varname, typ, substitution exp' v x)
	| If(e1, e2, e3) -> If(substitution e1 v x, substitution e2 v x, substitution e3 v x) 
	| App(e1, e2) -> App(substitution e1 v x, substitution e2 v x)
	| Add(e1, e2) -> Add(substitution e1 v x, substitution e2 v x)
	| Mult(e1, e2) -> Mult(substitution e1 v x, substitution e2 v x)
	| IsZero(v) -> IsZero(v)
	| Pair(e1, e2) -> Pair(substitution e1 v x, substitution e2 v x)
	| Fst(e1) -> Fst(substitution e v x)
	| Snd(e1) -> Snd(substitution e v x)
	| AddFloat(e1, e2) -> AddFloat(substitution e1 v x, substitution e2 v x)
	| MultFloat(e1, e2) -> MultFloat(substitution e1 v x, substitution e2 v x)
	| Ref(e) -> (substitution e v x)
	| DeRef(e) -> (substitution e v x)
	| None -> None
	| Some(v) -> Some(v) 
	(* | Let(varname, e1, e2) -> if varname = x then e2 else e2 *)

let rec subtyping t1 t2 =
	match (t1, t2) with
	| (Bool, Bool) -> true
	| (TypeInt, TypeInt) -> true
	| (TypeInt, TypeFloat) -> true
	| (TypeFloat, TypeInt) -> true
	| (Fun(typ1, typ2), Fun(typ3, typ4)) -> subtyping typ3 typ1 && subtyping typ2 typ4
	(* | Let(_, _, _) -> true *)
	| otherwise -> false

let rec type_checker gamma e = 
	match e with
	(* Var(x) -> lookup gamma x *)
	| True -> Bool
	| False -> Bool
	| Int(v) -> TypeInt
	| Float(v) -> TypeFloat
	| Var(e) -> TypeVar
	| App(e1, e2) -> (match type_checker gamma e1 with | Fun(t1, t2) -> if subtyping (type_checker gamma e2) t1 then t1 else t2)
	| Add(e1, e2) -> if (type_checker gamma e1 = TypeInt && type_checker gamma e2 = TypeInt) then TypeInt else raise(Failure "Add: not a compatible type")
	| Mult(e1, e2) -> if (type_checker gamma e1 = TypeInt && type_checker gamma e2 = TypeInt) then TypeInt else raise(Failure "Mult: not a compatible type" )
	| AddFloat(e1, e2) -> if (type_checker gamma e1 = TypeFloat && type_checker gamma e2 = TypeFloat) then TypeFloat else raise(Failure "AddFloat: not a compatible type" )
	| MultFloat(e1, e2) -> if (type_checker gamma e1 = TypeFloat && type_checker gamma e2 = TypeFloat) then TypeFloat else raise(Failure "MultFloat: not a compatible type" )
	| Pair(e1, e2) -> if (type_checker gamma e1 = type_checker gamma e2) then TypePair else raise(Failure "Pair: not a compatible type" )
	| IsZero(e) -> if (type_checker gamma e = TypeInt) then Bool else raise(Failure "IsZero: not a compatibe type")
	| If(e1, e2, e3) -> if(type_checker gamma e1 = Bool && (type_checker gamma e2 = type_checker gamma e3)) then Bool else raise(Failure "If-then-else: not a compatible type")
	| Fst(e) -> type_checker gamma e
	| Snd(e) -> type_checker gamma e
	| Lambda(v, e2, e3) -> raise(Failure "Lambda: not a compatible type")
	| otherwise -> raise(Failure "Type_checker: match not found")

let rec myiterator v clauses =
	match clauses with
			| [] -> Error
			(* | ((pattern, body)) :: restOfTheList -> match Match(v,pattern) with 
																										| None -> myiterator v restOfTheList 
																										| Some bindings -> eval(multiple_subst body bindings) *)

let rec evaluator exp = 
	match exp with 
	| True -> True
	| False -> False
	| Int(v) -> Int(v)
	| Float(v) -> Float(v)
	| Lambda(varname, typ, exp') -> Lambda(varname, typ, exp')
	| If(e1, e2, e3) -> if evaluator e1 = True 
							then evaluator e2 
							else if evaluator e1 = False then evaluator e3 else raise(Failure "If: guard is neither true or false")
	| App(e1, e2) -> (match evaluator e1 with 
									| Lambda(varname, typ, exp') -> let v = evaluator e2 in 
																	let mysubt = substitution exp' v varname in 
																	evaluator mysubt
									| _ -> raise(Failure "App: first arg is not a function"))
	(* | Fun(e1, e2) -> Fun(e1, e2) *)
	| IsZero(e1) -> (match evaluator e1 with Int(v1) -> if v1 = 0 then True else False | _-> raise(Failure "IsZero: not the right type"))
	| Add(e1, e2) -> (match (evaluator e1, evaluator e2) with | (Int(i1),Int(i2)) -> Int(i1 + i2) | _-> raise(Failure "Add: not the right type"))
	| Add(e1, e2) -> (match evaluator e1 with Int(v1) -> (match evaluator e2 with Int(v2) -> Int(v1+v2)| _ -> raise(Failure "not an int")) | _ -> raise(Failure "not an int"))
	| Mult(e1, e2) -> (match (evaluator e1, evaluator e2) with | (Int(i1), Int(i2)) -> Int(i1 * i2) | _-> raise(Failure "Mult: not the right type"))
	| AddFloat(e1, e2) -> (match (evaluator e1, evaluator e2) with | (Float(i1),Float(i2)) -> Float(i1 +. i2) | _-> raise(Failure "AddFloat: not the right type"))
	| MultFloat(e1, e2) -> (match (evaluator e1, evaluator e2) with | (Float(i1), Float(i2)) -> Float(i1 *. i2) | _-> raise(Failure "MultFloat: not the right type"))
	| Pair(e1, e2) -> (match (evaluator e1, evaluator e2) with | _ ->Pair(evaluator e1, evaluator e2))
	| Fst(e) -> (match e with Pair(e1,e2) -> evaluator e1)
	| Snd(e) -> (match e with Pair(e1,e2) -> evaluator e2)
	| Match(e, clauses) -> myiterator( evaluator e) clauses
	(* | Let(x, e1, e2) -> evaluator (substitution (evaluator e1) x e2) *)

let rec eval (e,s) = 
	match e with 
	| True -> (True, s)
	| False -> (False, s)
	| Int(v) -> (Int(v), s)
	| Float(v) -> (Float(v), s)
	| Lambda(varname, typ, exp') -> (Lambda(varname, typ, exp'), s)
	(* | Ref(e) -> let (v, s) = eval(e, s) in
							let c = Store.fresh() in 
							(c, Store.modify(s, c, v))
	| DeRef(e) -> let (v, mem') = eval e mem in
									mylist = getAllKeys mem'
									n = getMax mylist 
									Label(n+1), (mem' @ [Label (n+1), v]) *)

let rec prettyPrinter_typ (t : typ) = 
	match t with 
	| Bool -> "Bool"
	| Fun(t1,t2) -> prettyPrinter_typ t1 ^ " --> " ^ prettyPrinter_typ t2
	| TypeInt -> "Int"
	| TypeFloat -> "Float"
	| TypePair -> "Pair"
	| otherwise -> raise(Failure "prettyPrinter_typ: Match not found")

let rec prettyPrinter_exp (exp : expression) = 
	match exp with 
	| True -> "True"
	| False -> "False"
	| Int(v) -> string_of_int  v
	| Float(v) -> string_of_float v
	| Var(varname) -> varname 
	| Lambda(varname, typ, exp') -> "Lambda " ^ varname ^ " : " ^ prettyPrinter_typ typ ^ "." ^ prettyPrinter_exp exp' 
	| App(exp1, exp2) -> "(" ^ prettyPrinter_exp exp1 ^ "  " ^ prettyPrinter_exp exp2 ^ ")"
	| If(exp1, exp2, exp3) -> "If " ^ prettyPrinter_exp exp1 ^ " then " ^ prettyPrinter_exp exp2 ^ " else " ^ prettyPrinter_exp exp3
  | IsZero(exp1) -> "IsZero " ^ prettyPrinter_exp exp1
	| Add(v1, v2) -> "Add " ^ prettyPrinter_exp v1 ^ " + " ^ prettyPrinter_exp v2
	| Mult(exp1, exp2) -> "Mult " ^ prettyPrinter_exp exp1 ^ " * " ^ prettyPrinter_exp exp2
	| AddFloat(exp1, exp2) -> "Add " ^ prettyPrinter_exp exp1 ^ " +. " ^ prettyPrinter_exp exp2
	| MultFloat(exp1, exp2) -> "Mult " ^ prettyPrinter_exp exp1 ^ " *. " ^ prettyPrinter_exp exp2
	| Pair(exp1, exp2) -> "Pair(" ^ prettyPrinter_exp exp1 ^ "," ^ prettyPrinter_exp exp2 ^ ")" 
	| Fst(exp) -> "First "  ^ prettyPrinter_exp exp
	| Snd(exp) -> "Second " ^ prettyPrinter_exp exp
	| otherwise -> raise(Failure "match not found ")

let prettyPrinter_exp_ln (exp : expression) = prettyPrinter_exp exp ^ "\n"

let prettyPrinter_typ_ln (t : typ) = prettyPrinter_typ t ^ "\n"

let main = 

(*  Test *)
print_string ("\n------------- Testing IsZero -------------\n");
print_string (prettyPrinter_exp_ln (If(IsZero(Int(3)), True, False)));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (If(IsZero(Int(3)), True, False))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (If(IsZero(Int(3)), True, False))));

print_string("\n");
print_string (prettyPrinter_exp_ln (If(IsZero(Int(0)), True, False)));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (If(IsZero(Int(0)), True, False))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (If(IsZero(Int(0)), True, False))));

print_string ("\n------------- Testing Addition -------------\n");
print_string (prettyPrinter_exp_ln (Add(Int(2), Int(3))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (Add(Int(2), Int(3)))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (Add(Int(2), Int(3)))));

print_string("\n");
print_string (prettyPrinter_exp_ln (AddFloat(Float(7.0), Float(3.5))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (AddFloat(Float(7.0), Float(3.5)))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (AddFloat(Float(7.0), Float(3.5)))));

(* print_string("\n");
print_string (prettyPrinter_exp_ln (Add(Float(7.0), Int(5))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (Add(Int(7), Int(5)))));
print_string "Type checker: ";	 *)
(* print_string (prettyPrinter_typ_ln (type_checker evaluator (Add(Int(7), Int(5)))))); *)

print_string ("\n------------- Testing Multiplication -------------\n");
print_string (prettyPrinter_exp_ln (Mult(Int(45), Int(3))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (Mult(Int(45), Int(3)))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (Mult(Int(45), Int(3)))));

print_string("\n");
print_string (prettyPrinter_exp_ln (MultFloat(Float(7.0), Float(3.5))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (MultFloat(Float(7.0), Float(3.5)))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (MultFloat(Float(7.0), Float(3.5)))));

print_string ("\n------------- Testing Pair, Fst and Snd -------------\n");
print_string (prettyPrinter_exp_ln (Fst(Pair(Int(10), Int(8)))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (Fst(Pair(Int(10), Int(8))))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (Fst(Pair(Int(10), Int(8))))));

print_string("\n");
print_string (prettyPrinter_exp_ln (Snd(Pair(Int(100), Int(48)))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (Snd(Pair(Int(100), Int(48))))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (Snd(Pair(Int(100), Int(48))))));

print_string ("\n------------- Testing Lambda -------------\n");

print_string (prettyPrinter_exp_ln (If(True, Lambda("x", Bool , Var("x")), Lambda("z", Bool , App(Var("z"),Var("z"))))));
print_string "Result: ";
print_string (prettyPrinter_exp_ln (evaluator (If(True, Lambda("x", Bool , Var("x")), Lambda("z", Bool , App(Var("z"),Var("z")))))));
print_string "Type checker: ";	
print_string (prettyPrinter_typ_ln (type_checker evaluator (If(True, Lambda("x", Bool , Var("x")), Lambda("z", Bool , App(Var("z"),Var("z")))))));
print_string ("\n");
print_string (prettyPrinter_exp_ln (If(True, (App(Lambda("x", Bool , Var("x")), True)), False)));
print_string "Result: ";
print_string (prettyPrinter_exp_ln (evaluator (If(True, (App(Lambda("x", Bool , Var("x")), True)), False))));

print_string ("\n------------- Testing  -------------\n");

(* print_string (prettyPrinter_exp_ln (If(IsZero(0), True, False)));
print_string "Result: ";	 *)
(* print_string (prettyPrinter_exp_ln (evaluator (If(IsZero(0), True, False)))); *)

print_string (prettyPrinter_exp_ln (If(True, Add(Int(1), Int(2)), Int(3))));
print_string "Result: ";	
print_string (prettyPrinter_exp_ln (evaluator (If(True, Add(Int(1), Int(2)), Int(3)))));

print_string (prettyPrinter_exp_ln (If(True, (App(Lambda("x", Bool , Var("x")), True)), False)));
print_string "Result: \n";
print_string (prettyPrinter_exp_ln (evaluator (If(True, (App(Lambda("x", Bool , Var("x")), True)), False))));
print_string (prettyPrinter_exp_ln (If(True, (App(Lambda("x", Bool , Var("x")), True)), False)));
print_string "Result: \n";
print_string (prettyPrinter_exp_ln (evaluator (If(True, (App(Lambda("x", Bool , Var("x")), True)), False))));
