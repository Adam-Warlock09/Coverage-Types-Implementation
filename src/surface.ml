(* The tree the parser builds: exactly what the user wrote.
   Nesting is allowed here (f (g x), a + b * c, if x && y ...).
   Elaborate turns it into the simpler core language. *)

type binop =
	| BAdd | BSub | BMul | BMod                  (* + - * mod      *)
	| BEq | BNeq | BLt | BLe | BGt | BGe         (* = <> < <= > >= *)
	| BAnd | BOr | BImplies | BIff               (* && || ==> <=>  *)

type sexpr =
	| EInt of int
	| EBool of bool
	| EVar of string
	| EErr
	| ECall of string * sexpr list               (* f a b,  or  f ()  with [] *)
	| EBin of binop * sexpr * sexpr
	| ENot of sexpr
	| ELet of string * sexpr * sexpr
	| EIf of sexpr * sexpr * sexpr

(* {x:int | p}  is KOver,   [x:int | p]  is KCover *)
type rkind = KOver | KCover

(* A refinement type as written: kind, binder name, sort, predicate.
   The predicate is a sexpr for now; elaborate checks it is pure logic. *)
type rty = TRef of rkind * string * Formula.sort * sexpr

(* let name (p1 : t1) (p2 : t2) : result = body *)
type def = {
	name : string;
	params : (string * rty) list;
	result : rty;
	body : sexpr;
	line : int;
}