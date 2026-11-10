open Formula

(* The three kinds of refinement types from the paper (Fig. 4):

   ROver  (s, φ)   =  {v:s | φ}   "may"  : the caller promises the value satisfies φ
   RCover (s, φ)   =  [v:s | φ]   "must" : the program can produce EVERY value satisfying φ
   RArrow (x, a, r) = x:a -> r    a function; r may mention the parameter x  *)
type t =
	| ROver of sort * formula
	| RCover of sort * formula
	| RArrow of string * t * t

(* Pretty printer, for debugging. *)
let rec show (ty : t) : string =
	match ty with
	| ROver (_, p) -> Printf.sprintf "{v | %s}" (to_smt p)
	| RCover (_, p) -> Printf.sprintf "[v | %s]" (to_smt p)
	| RArrow (x, a, r) -> Printf.sprintf "%s:%s -> %s" x (show a) (show r)

(* Turn "variable name has type ty" into a context binding.
   The type talks about v, the binding must talk about name, so we rename. *)
let bind (name : string) (ty : t) : Context.binding =
	match ty with
	| ROver (s, p) ->
		{ Context.name = name; sort = s; kind = Context.Over; pred = rename "v" name p }
	| RCover (s, p) ->
		{ Context.name = name; sort = s; kind = Context.Cover; pred = rename "v" name p }
	| RArrow _ ->
		failwith "bind: function-typed variables don't go into the logical context"

(* Extend a context with x : ty. Function-typed variables are skipped,
   because Z3 formulas can't talk about functions (paper, Algorithm 1). *)
let extend (ctx : Context.t) (x : string) (ty : t) : Context.t =
	match ty with
	| RArrow _ -> ctx
	| _ -> ctx @ [ bind x ty ]

(* ---------- 1. Subtyping  ---------- *)

let rec subtype (ctx : Context.t) (t1 : t) (t2 : t) : bool =
	match t1, t2 with
	(* must-types: the producible set must contain the target set *)
	| RCover (s1, p1), RCover (s2, p2) when s1 = s2 ->
		Context.subtype ctx ~vsort:s1 p1 p2
	(* may-types: the usual direction, p1 => p2 (arguments swapped on purpose) *)
	| ROver (s1, p1), ROver (s2, p2) when s1 = s2 ->
		Context.subtype ctx ~vsort:s1 p2 p1
	(* functions: argument flipped, result normal, result checked with x in scope.
	   For now both functions must use the same parameter name. *)
	| RArrow (x1, a1, r1), RArrow (x2, a2, r2) when x1 = x2 ->
		subtype ctx a2 a1 && subtype (extend ctx x2 a2) r1 r2
	| _ -> false

(* ---------- 2. Well-formedness ---------- *)

let rec well_formed (ctx : Context.t) (ty : t) : bool =
	match ty with
	| ROver _ | RCover _ -> Context.feasible ctx
	| RArrow (x, a, r) ->
		(* WfArg: parameters are may-types (or functions), never must-types *)
		let arg_ok = (match a with RCover _ -> false | _ -> true) in
		(* WfRes: results are must-types (or functions), never may-types *)
		let res_ok = (match r with ROver _ -> false | _ -> true) in
		arg_ok && res_ok && well_formed ctx a && well_formed (extend ctx x a) r

(* ---------- 3. Disjunction (merging two branches) ---------- *)

(* Branch 1 can produce φ1, branch 2 can produce φ2,
   so together they can produce φ1 ∨ φ2. *)
let disj (t1 : t) (t2 : t) : t =
	match t1, t2 with
	| RCover (s1, p1), RCover (s2, p2) when s1 = s2 -> RCover (s1, Or (p1, p2))
	| _ -> failwith "disj: can only merge two must-types of the same sort"

(* ---------- 4. Hiding a variable ---------- *)

(* A branch's type may mention a local or ghost variable that won't exist
   outside the branch. We fold that variable's fact into the type:
     [v | φ]   becomes   [v | ∃b. (fact about b) ∧ φ]                  *)
let hide (b : Context.binding) (ty : t) : t =
	match b.Context.kind, ty with
	| Context.Cover, RCover (s, p) ->
		RCover (s, Exists (b.Context.name, b.Context.sort, And (b.Context.pred, p)))
	| _ -> failwith "hide: only generator-chosen variables can be hidden from a must-type"

(* ---------- 5. Renaming inside a type ---------- *)

(* Replace variable x by y everywhere in a type.
   If an arrow's own parameter is called x, the x after it is a different x: stop. *)
let rec rename_ty (x : string) (y : string) (ty : t) : t =
	match ty with
	| ROver (s, p) -> ROver (s, rename x y p)
	| RCover (s, p) -> RCover (s, rename x y p)
	| RArrow (z, a, r) ->
		RArrow (z, rename_ty x y a, if z = x then r else rename_ty x y r)