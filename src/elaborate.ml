open Formula
open Expr
open Surface

module R = Rtype
module T = Typecheck

exception Elab_error of string
let fail msg = raise (Elab_error msg)

type senv = (string * sort) list

let lookup (env : senv) (x : string) : sort =
	match List.assoc_opt x env with
	| Some s -> s
	| None -> fail ("unbound variable " ^ x)

let reserved (x : string) : unit =
	if x = "v" then fail "the name v is reserved for 'the value being produced'"

(* ================= 1. Refinement predicates -> formulas ================= *)

let pred_sort (env : senv) (e : sexpr) : sort =
	match e with
	| EInt _ -> SInt
	| EBool _ -> SBool
	| EVar x -> lookup env x
	| EBin ((BAdd | BSub | BMul | BMod), _, _) -> SInt
	| EBin _ | ENot _ -> SBool
	| EErr | ECall _ | ELet _ | EIf _ ->
		fail "only arithmetic and logic are allowed inside a refinement"

let rec to_term (env : senv) (e : sexpr) : term =
	match e with
	| EInt n -> Num n
	| EVar x when lookup env x = SInt -> Var x
	| EBin (BAdd, a, b) -> Add (to_term env a, to_term env b)
	| EBin (BSub, a, b) -> Sub (to_term env a, to_term env b)
	| EBin (BMul, a, b) -> Mul (to_term env a, to_term env b)
	| EBin (BMod, a, b) -> Mod (to_term env a, to_term env b)
	| _ -> fail "expected a number expression inside a refinement"

let rec to_formula (env : senv) (e : sexpr) : formula =
	let f = to_formula env and t = to_term env in
	match e with
	| EBool true -> True
	| EBool false -> False
	| EVar x when lookup env x = SBool -> BVar x
	| ENot a -> Not (f a)
	| EBin (BAnd, a, b) -> And (f a, f b)
	| EBin (BOr, a, b) -> Or (f a, f b)
	| EBin (BImplies, a, b) -> Implies (f a, f b)
	| EBin (BIff, a, b) -> Iff (f a, f b)
	(* = between bools means <=>, between ints means = *)
	| EBin (BEq, a, b) when pred_sort env a = SBool -> Iff (f a, f b)
	| EBin (BNeq, a, b) when pred_sort env a = SBool -> Not (Iff (f a, f b))
	| EBin (BEq, a, b) -> Eq (t a, t b)
	| EBin (BNeq, a, b) -> Not (Eq (t a, t b))
	| EBin (BLt, a, b) -> Lt (t a, t b)
	| EBin (BLe, a, b) -> Le (t a, t b)
	| EBin (BGt, a, b) -> Gt (t a, t b)
	| EBin (BGe, a, b) -> Ge (t a, t b)
	| _ -> fail "expected a true/false expression inside a refinement"

(* ================= 2. Types ================= *)

let sort_of_rty (TRef (_, _, s, _)) : sort = s

(* {x:int | p}  ->  ROver (SInt, p with x renamed to v) *)
let to_rtype (env : senv) (TRef (k, binder, s, p)) : R.t =
	let phi = rename binder "v" (to_formula ((binder, s) :: env) p) in
	match k with
	| KOver -> R.ROver (s, phi)
	| KCover -> R.RCover (s, phi)

(* (x : t1) (y : t2) : r   ->   x:t1 -> y:t2 -> r *)
let def_type (d : def) : R.t =
	let rec go env params =
		match params with
		| [] -> to_rtype env d.result
		| (x, t) :: rest ->
			reserved x;
			let a = to_rtype env t in
			R.RArrow (x, a, go ((x, sort_of_rty t) :: env) rest)
	in
	go [] d.params

(* ================= 3. Program bodies -> core expressions ================= *)

(* function signatures: parameter sorts and result sort *)
type sigs = (string * (sort list * sort)) list

let lookup_sig (sigs : sigs) (f : string) : sort list * sort =
	match f with
	| "int_gen" -> ([], SInt)
	| "bool_gen" -> ([], SBool)
	| _ ->
		match List.assoc_opt f sigs with
		| Some s -> s
		| None -> fail ("unknown function " ^ f)

(* The sort of a program expression. None means "only err", unknown so far. *)
let rec prog_sort (sigs : sigs) (env : senv) (e : sexpr) : sort option =
	match e with
	| EInt _ -> Some SInt
	| EBool _ -> Some SBool
	| EVar x -> Some (lookup env x)
	| EErr -> None
	| ECall (f, _) -> Some (snd (lookup_sig sigs f))
	| EBin ((BAdd | BSub | BMul | BMod), _, _) -> Some SInt
	| EBin _ | ENot _ -> Some SBool
	| ELet (x, e1, e2) ->
		let s1 = Option.value (prog_sort sigs env e1) ~default:SInt in
		prog_sort sigs ((x, s1) :: env) e2
	| EIf (_, a, b) ->
		(match prog_sort sigs env a with
		 | Some s -> Some s
		 | None -> prog_sort sigs env b)

(* fresh names for temporaries; '$' can't appear in user names *)
let counter = ref 0
let fresh () : string =
	incr counter;
	Printf.sprintf "tmp$%d" !counter

let int_op (op : binop) : op =
	match op with
	| BAdd -> Plus | BSub -> Minus | BMul -> Times | BMod -> Modulo
	| BEq -> Equal | BLt -> Less | BLe -> LessEq | BGt -> Greater | BGe -> GreaterEq
	| _ -> fail "not an integer operator"

(* norm: turn a surface expression into a core expression.
   expected = the sort this expression should have (used to give err its sort). *)
let rec norm (sigs : sigs) (env : senv) (expected : sort) (e : sexpr) : expr =
	let norm_here = norm sigs env expected in
	match e with
	| EInt n -> Atom (AInt n)
	| EBool b -> Atom (ABool b)
	| EVar x -> ignore (lookup env x); Atom (AVar x)
	| EErr -> Err expected

	| ECall (("int_gen" | "bool_gen") as f, args) ->
		if args <> [] then fail (f ^ " takes ()");
		Gen (snd (lookup_sig sigs f))
	| ECall (f, args) ->
		let (psorts, _) = lookup_sig sigs f in
		if List.length psorts <> List.length args then
			fail (Printf.sprintf "%s expects %d argument(s)" f (List.length psorts));
		atomize_list sigs env psorts args (fun atoms -> App (f, atoms))

	(* boolean operators become if-then-else *)
	| EBin (BAnd, a, b) -> norm_here (EIf (a, b, EBool false))
	| EBin (BOr, a, b) -> norm_here (EIf (a, EBool true, b))
	| EBin (BImplies, a, b) -> norm_here (EIf (a, b, EBool true))
	| EBin (BIff, a, b) -> norm_here (EIf (a, b, ENot b))
	| ENot a -> norm_here (EIf (a, EBool false, EBool true))
	| EBin (BEq, a, b)
		when prog_sort sigs env a = Some SBool || prog_sort sigs env b = Some SBool ->
		norm_here (EIf (a, b, ENot b))
	| EBin (BNeq, a, b) -> norm_here (ENot (EBin (BEq, a, b)))

	(* integer operators: both sides become atoms first *)
	| EBin (((BAdd | BSub | BMul | BMod | BEq | BLt | BLe | BGt | BGe) as op), a, b) ->
		atomize sigs env SInt a (fun x ->
		atomize sigs env SInt b (fun y ->
		Prim (int_op op, x, y)))

	| ELet (x, e1, e2) ->
		reserved x;
		let s1 = Option.value (prog_sort sigs env e1) ~default:SInt in
		Let (x, norm sigs env s1 e1, norm sigs ((x, s1) :: env) expected e2)

	| EIf (c, a, b) ->
		atomize sigs env SBool c (fun ca -> If (ca, norm_here a, norm_here b))

(* atomize: if e is already an atom, hand it to k directly.
   Otherwise:  let tmp = <e> in k tmp  *)
and atomize (sigs : sigs) (env : senv) (expected : sort) (e : sexpr) (k : atom -> expr) : expr =
	match e with
	| EInt n -> k (AInt n)
	| EBool b -> k (ABool b)
	| EVar x -> ignore (lookup env x); k (AVar x)
	| _ ->
		let s = Option.value (prog_sort sigs env e) ~default:expected in
		let t = fresh () in
		Let (t, norm sigs env s e, k (AVar t))

and atomize_list sigs env sorts es (k : atom list -> expr) : expr =
	match sorts, es with
	| [], [] -> k []
	| s :: ss, e :: rest ->
		atomize sigs env s e (fun a -> atomize_list sigs env ss rest (fun atoms -> k (a :: atoms)))
	| _ -> fail "wrong number of arguments"

(* ================= 4. Whole file ================= *)

(* For each definition: its name, line, and either the core definition or an error.
   A definition's signature is recorded even if its body has an error,
   so later definitions can still call it. *)
let elaborate (defs : def list) : (string * int * (T.def, string) result) list =
	let (_, out) =
		List.fold_left
			(fun (sigs, acc) (d : def) ->
				let env = List.map (fun (x, t) -> (x, sort_of_rty t)) d.params in
				let rs = sort_of_rty d.result in
				let r =
					try Ok { T.name = d.name; ty = def_type d; body = norm sigs env rs d.body }
					with Elab_error msg -> Error msg
				in
				((d.name, (List.map snd env, rs)) :: sigs, acc @ [ (d.name, d.line, r) ]))
			([], []) defs
	in
	out