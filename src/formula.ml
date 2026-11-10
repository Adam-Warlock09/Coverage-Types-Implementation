(* The kinds of values a variable can hold. *)
type sort =
	| SInt
	| SBool

(* A "term" is something that produces a number: x, 5, x + 1, x mod 2 ... *)
type term =
	| Var of string			(* a variable, e.g. Var "x" *)
	| Num of int			(* a number, e.g. Num 5 *)
	| Add of term * term	(* a + b *)
	| Sub of term * term	(* a - b *)
	| Mul of term * term	(* a * b *)
	| Mod of term * term	(* a mod b *)

(* A "formula" is something that is true or false. *)
type formula =
	| True
	| False
	| BVar of string						(* a boolean variable, e.g. BVar "b" *)
	| Eq of term * term						(* a = b *)
	| Lt of term * term						(* a < b *)
	| Le of term * term						(* a <= b *)
	| Gt of term * term						(* a > b *)
	| Ge of term * term						(* a >= b *)
	| Not of formula						(* not f *)
	| Or of formula * formula				(* f1 or f2 *)
	| And of formula * formula				(* f1 and f2 *)
	| Implies of formula * formula			(* f1 => f2 *)
	| Iff of formula * formula				(* f1 <=> f2 *)
	| Forall of string * sort * formula		(* forall x: T, f(x) *)
	| Exists of string * sort * formula		(* exists x: T, f(x) *)

(* ---------- Printing to Z3's language ---------- *)

let sort_to_smt = function 
	| SInt -> "Int"
	| SBool -> "Bool"

let rec term_to_smt (t : term) : string = 
	match t with
	| Var x -> x
	| Num n ->
		(* Z3 does not accept "-5"; it wants "(- 5)" *)
      	if n < 0 then Printf.sprintf "(- %d)" (-n) else string_of_int n
	| Add (a, b) -> Printf.sprintf "(+ %s %s)" (term_to_smt a) (term_to_smt b)
	| Sub (a, b) -> Printf.sprintf "(- %s %s)" (term_to_smt a) (term_to_smt b)
	| Mul (a, b) -> Printf.sprintf "(* %s %s)" (term_to_smt a) (term_to_smt b)
	| Mod (a, b) -> Printf.sprintf "(mod %s %s)" (term_to_smt a) (term_to_smt b)

let rec to_smt (f : formula) : string = 
	match f with
	| True -> "true"
	| False -> "false"
	| BVar x -> x
	| Eq (a, b) -> Printf.sprintf "(= %s %s)" (term_to_smt a) (term_to_smt b)
	| Lt (a, b) -> Printf.sprintf "(< %s %s)" (term_to_smt a) (term_to_smt b)
	| Le (a, b) -> Printf.sprintf "(<= %s %s)" (term_to_smt a) (term_to_smt b)
	| Gt (a, b) -> Printf.sprintf "(> %s %s)" (term_to_smt a) (term_to_smt b)
	| Ge (a, b) -> Printf.sprintf "(>= %s %s)" (term_to_smt a) (term_to_smt b)
	| Not f -> Printf.sprintf "(not %s)" (to_smt f)
	| Or (a, b) -> Printf.sprintf "(or %s %s)" (to_smt a) (to_smt b)
	| And (a, b) -> Printf.sprintf "(and %s %s)" (to_smt a) (to_smt b)
	| Implies (a, b) -> Printf.sprintf "(=> %s %s)" (to_smt a) (to_smt b)
	| Iff (a, b) -> Printf.sprintf "(= %s %s)" (to_smt a) (to_smt b)
	| Forall (x, s, body) -> Printf.sprintf "(forall ((%s %s)) %s)" x (sort_to_smt s) (to_smt body)
	| Exists (x, s, body) -> Printf.sprintf "(exists ((%s %s)) %s)" x (sort_to_smt s) (to_smt body)

(* ---------- Asking Z3 ---------- *)

let valid (f : formula) : bool =
  	Z3.valid ~vars:[] (to_smt f)

(* ---------- Renaming a variable ---------- *)

(* rename x y f : replace every free occurrence of x in f by y.
   We assume y is a fresh name that isn't already used inside f. *)
let rec rename_term (x : string) (y : string) (t : term) : term =
	match t with
	| Var z -> if z = x then Var y else t
	| Num _ -> t
	| Add (a, b) -> Add (rename_term x y a, rename_term x y b)
	| Sub (a, b) -> Sub (rename_term x y a, rename_term x y b)
	| Mul (a, b) -> Mul (rename_term x y a, rename_term x y b)
	| Mod (a, b) -> Mod (rename_term x y a, rename_term x y b)

let rec rename (x : string) (y : string) (f : formula) : formula =
	let r = rename x y in
	let rt = rename_term x y in
	match f with
	| True | False -> f
	| BVar z -> if z = x then BVar y else f
	| Eq (a, b) -> Eq (rt a, rt b)
	| Lt (a, b) -> Lt (rt a, rt b)
	| Le (a, b) -> Le (rt a, rt b)
	| Gt (a, b) -> Gt (rt a, rt b)
	| Ge (a, b) -> Ge (rt a, rt b)
	| Not g -> Not (r g)
	| Or (a, b) -> Or (r a, r b)
	| And (a, b) -> And (r a, r b)
	| Implies (a, b) -> Implies (r a, r b)
	| Iff (a, b) -> Iff (r a, r b)
	(* if a quantifier re-binds x, the x inside is a different x: stop *)
	| Forall (z, s, body) -> if z = x then f else Forall (z, s, r body)
	| Exists (z, s, body) -> if z = x then f else Exists (z, s, r body)