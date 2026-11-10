open Formula
open Expr

module R = Rtype

exception Type_error of string
let fail msg = raise (Type_error msg)

(* Fresh names for ghost variables: ghost1, arg2, ... *)
let counter = ref 0
let fresh (base : string) : string =
	incr counter;
	Printf.sprintf "%s%d" base !counter

(* NEW: the function environment, i.e. the declared functions and their types.
   Kept separate from the logical context, because Z3 formulas
   can't talk about functions. *)
type fenv = (string * R.t) list

let lookup_fun (fenv : fenv) (f : string) : R.t =
	match List.assoc_opt f fenv with
	| Some ty -> ty
	| None -> fail ("unknown function " ^ f)

(* ---------- Looking things up ---------- *)

let sort_of_var (ctx : Context.t) (x : string) : sort =
	match List.find_opt (fun b -> b.Context.name = x) (List.rev ctx) with
	| Some b -> b.Context.sort
	| None -> fail ("unbound variable " ^ x)

let atom_sort (ctx : Context.t) (a : atom) : sort =
	match a with
	| AInt _ -> SInt
	| ABool _ -> SBool
	| AVar x -> sort_of_var ctx x

let int_term (ctx : Context.t) (a : atom) : term =
	match a with
	| AInt n -> Num n
	| AVar x when sort_of_var ctx x = SInt -> Var x
	| _ -> fail ("expected an int, got " ^ show_atom a)

let bool_formula (ctx : Context.t) (a : atom) : formula =
	match a with
	| ABool true -> True
	| ABool false -> False
	| AVar x when sort_of_var ctx x = SBool -> BVar x
	| _ -> fail ("expected a bool, got " ^ show_atom a)

let v = Var "v"
let bv = BVar "v"

(* ---------- Types of the simple pieces ---------- *)

(* The fact "v equals this atom". *)
let atom_fact (ctx : Context.t) (a : atom) : formula =
	match atom_sort ctx a with
	| SInt -> Eq (v, int_term ctx a)
	| SBool -> Iff (bv, bool_formula ctx a)

let type_of_atom (ctx : Context.t) (a : atom) : R.t =
	R.RCover (atom_sort ctx a, atom_fact ctx a)

let type_of_prim (ctx : Context.t) (op : op) (a : atom) (b : atom) : R.t =
	let t1 = int_term ctx a in
	let t2 = int_term ctx b in
	match op with
	| Plus      -> R.RCover (SInt, Eq (v, Add (t1, t2)))
	| Minus     -> R.RCover (SInt, Eq (v, Sub (t1, t2)))
	| Times     -> R.RCover (SInt, Eq (v, Mul (t1, t2)))
	| Modulo    -> R.RCover (SInt, Eq (v, Mod (t1, t2)))
	| Equal     -> R.RCover (SBool, Iff (bv, Eq (t1, t2)))
	| Less      -> R.RCover (SBool, Iff (bv, Lt (t1, t2)))
	| LessEq    -> R.RCover (SBool, Iff (bv, Le (t1, t2)))
	| Greater   -> R.RCover (SBool, Iff (bv, Gt (t1, t2)))
	| GreaterEq -> R.RCover (SBool, Iff (bv, Ge (t1, t2)))

let sort_of_type (ty : R.t) : sort =
	match ty with
	| R.RCover (s, _) | R.ROver (s, _) -> s
	| R.RArrow _ -> fail "expected a base type, got a function type"

(* ---------- Synthesis ---------- *)

let rec synth (fenv : fenv) (ctx : Context.t) (e : expr) : R.t =
	match e with
	| Atom a -> type_of_atom ctx a
	| Err s -> R.RCover (s, False)
	| Gen s -> R.RCover (s, True)
	| Prim (op, a, b) -> type_of_prim ctx op a b

	| Let (x, e1, e2) ->
		let t1 = synth fenv ctx e1 in
		let bx = R.bind x t1 in
		let t2 = synth fenv (ctx @ [ bx ]) e2 in
		R.hide bx t2

	| If (c, e1, e2) ->
		let cond = bool_formula ctx c in
		let ghost fact = R.bind (fresh "ghost") (R.RCover (SBool, And (Iff (bv, cond), fact))) in
		let g_then = ghost bv in
		let g_else = ghost (Not bv) in
		let t_then = R.hide g_then (synth fenv (ctx @ [ g_then ]) e1) in
		let t_else = R.hide g_else (synth fenv (ctx @ [ g_else ]) e2) in
		if sort_of_type t_then <> sort_of_type t_else then
			fail "the two branches of an if have different sorts";
		R.disj t_then t_else

	(* NEW: calling a declared function (paper rule SynAppBase).
	   Walk the function's type one parameter at a time. For each argument:
	     - make a fresh ghost g whose fact is  g = arg  AND  g satisfies the
	       parameter's promise
	     - rename the parameter to g in the rest of the type
	   At the end, hide all the ghosts (first ghost outermost). *)
	| App (f, args) ->
		let rec walk (ty : R.t) (args : atom list) : Context.binding list * R.t =
			match ty, args with
			| R.RArrow (x, R.ROver (s, promise), rest), a :: more ->
				if atom_sort ctx a <> s then
					fail (Printf.sprintf "argument %s of %s has the wrong sort" (show_atom a) f);
				let g = fresh "arg" in
				let bg = R.bind g (R.RCover (s, And (atom_fact ctx a, promise))) in
				let (ghosts, result) = walk (R.rename_ty x g rest) more in
				(bg :: ghosts, result)
			| R.RArrow _, _ :: _ ->
				fail ("function-typed parameters are not supported yet (in " ^ f ^ ")")
			| R.RArrow _, [] ->
				fail ("partial application of " ^ f ^ " is not supported")
			| R.RCover _, [] -> ([], ty)
			| R.ROver _, [] -> fail ("the result type of " ^ f ^ " must be [v | ...]")
			| (R.RCover _ | R.ROver _), _ :: _ -> fail ("too many arguments to " ^ f)
		in
		let (ghosts, result) = walk (lookup_fun fenv f) args in
		List.fold_right R.hide ghosts result

(* ---------- Checking ---------- *)

let context_of_params (params : (string * R.t) list) : Context.t =
	List.fold_left (fun ctx (x, ty) -> R.extend ctx x ty) [] params

(* fenv is optional so the Step 4 tests still compile unchanged *)
let check ?(fenv = []) (ctx : Context.t) (e : expr) (target : R.t) : bool =
	if not (R.well_formed ctx target) then
		fail "target type is not well-formed in this context";
	R.subtype ctx (synth fenv ctx e) target

(* ---------- NEW: function definitions ---------- *)

(* A declared function: its name, its full type, and its body.
   The parameter names come from the arrows in the type. *)
type def = {
	name : string;
	ty : R.t;
	body : expr;
}

(* Check one definition (paper rule TFun):
   put every parameter in the context as caller-chosen,
   then check the body against the result type. *)
let check_def (fenv : fenv) (d : def) : bool =
	if not (R.well_formed [] d.ty) then
		fail ("the type of " ^ d.name ^ " is not well-formed");
	let rec open_params (ty : R.t) (ctx : Context.t) : Context.t * R.t =
		match ty with
		| R.RArrow (x, (R.ROver _ as a), r) -> open_params r (R.extend ctx x a)
		| R.RArrow _ -> fail "function-typed parameters are not supported yet"
		| R.RCover _ -> (ctx, ty)
		| R.ROver _ -> fail ("the result type of " ^ d.name ^ " must be [v | ...]")
	in
	let (ctx, result) = open_params d.ty [] in
	check ~fenv ctx d.body result

(* Check a whole program, in order. Each definition can call the earlier ones.

   Like the paper, this is modular: a call only trusts the callee's TYPE.
   A definition that fails its check is still added, so later definitions
   are judged against what it claims. Each failure stays local to its own
   definition. *)
let check_program (defs : def list) : (string * (bool, string) result) list =
	let (_, results) =
		List.fold_left
			(fun (fenv, acc) d ->
				let r = try Ok (check_def fenv d) with Type_error msg -> Error msg in
				((d.name, d.ty) :: fenv, acc @ [ (d.name, r) ]))
			([], []) defs
	in
	results