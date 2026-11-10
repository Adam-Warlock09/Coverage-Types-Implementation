open Formula

(* Things that need no computation: a number, true/false, or a variable. *)
type atom =
	| AInt of int
	| ABool of bool
	| AVar of string

(* Operators. Arithmetic gives an int; comparisons give a bool.
   All of them take two ints. *)
type op =
	| Plus | Minus | Times | Modulo
	| Equal | Less | LessEq | Greater | GreaterEq

type expr =
	| Atom of atom                   (* 5, true, x *)
	| Err of sort                    (* err  (the sort says int-err or bool-err) *)
	| Gen of sort                    (* int_gen () or bool_gen () *)
	| Prim of op * atom * atom       (* x + 1, n mod 2, lo <= x *)
	| Let of string * expr * expr    (* let x = e1 in e2 *)
	| If of atom * expr * expr       (* if b then e1 else e2 *)
	| App of string * atom list      (* f a b : call a declared function *)

(* ---------- Printing ---------- *)

let show_atom (a : atom) : string =
	match a with
	| AInt n -> string_of_int n
	| ABool b -> string_of_bool b
	| AVar x -> x

let show_op (op : op) : string =
	match op with
	| Plus -> "+" | Minus -> "-" | Times -> "*" | Modulo -> "mod"
	| Equal -> "==" | Less -> "<" | LessEq -> "<="
	| Greater -> ">" | GreaterEq -> ">="

let rec show (e : expr) : string =
	match e with
	| Atom a -> show_atom a
	| Err _ -> "err"
	| Gen SInt -> "int_gen ()"
	| Gen SBool -> "bool_gen ()"
	| Prim (op, a, b) -> Printf.sprintf "%s %s %s" (show_atom a) (show_op op) (show_atom b)
	| Let (x, e1, e2) -> Printf.sprintf "let %s = %s in %s" x (show e1) (show e2)
	| If (c, e1, e2) -> Printf.sprintf "(if %s then %s else %s)" (show_atom c) (show e1) (show e2)
	| App (f, args) -> String.concat " " (f :: List.map show_atom args)