open Formula

(* Over  = the caller picks the value, so we must handle ALL cases  (∀)
Cover = the generator picks the value, so SOME choice may work   (∃) *)
type kind =
	| Over
	| Cover

(* One fact about one variable.
"pred" is written directly in terms of the variable's own name.
Example: for b, pred is  b <=> (n mod 2 = 0). *)
type binding = {
	name : string;
	sort : sort;
	kind : kind;
	pred : formula;
}

(* A context is a list of bindings, oldest first. *)
type t = binding list

(* Split the context into caller-chosen and generator-chosen variables.
Order inside each group is kept (oldest first). *)
let split (ctx : t) : t * t =
	( List.filter (fun b -> b.kind = Over) ctx,
		List.filter (fun b -> b.kind = Cover) ctx )

(* Put "for every caller choice ..." around a formula, oldest outermost. *)
let forall_overs (overs : t) (body : formula) : formula =
	List.fold_right
		(fun b acc -> Forall (b.name, b.sort, Implies (b.pred, acc)))
		overs body

(* Wrap two formulas inside one generator-chosen binding's ∃. *)
let wrap_cover (b : binding) ((p1, p2) : formula * formula) : formula * formula =
	( Exists (b.name, b.sort, And (b.pred, p1)),
		Exists (b.name, b.sort, And (b.pred, p2)) )

(* The query: "under this context, does [v | phi1] cover [v | phi2]?"
phi1 = what the program is able to produce
phi2 = what we want it to produce (the target)

Shape of the formula:
∀ caller vars.  ∀v. (∃ gen vars. target)  ⇒  (∃ gen vars. produced) *)
let query (ctx : t) ~(vsort : sort) (phi1 : formula) (phi2 : formula) : formula =
	let (overs, covers) = split ctx in
	let (p1, p2) = List.fold_right wrap_cover covers (phi1, phi2) in
	forall_overs overs (Forall ("v", vsort, Implies (p2, p1)))

(* Ask Z3 whether the query is true. *)
let subtype (ctx : t) ~(vsort : sort) (phi1 : formula) (phi2 : formula) : bool =
	valid (query ctx ~vsort phi1 phi2)

(* Is this context a real execution path?
For EVERY choice the caller makes, the generator must be able to make
SOME choices that satisfy all its facts.
	∀ caller vars.  ∃ gen vars.  (all gen facts hold)*)
let feasible (ctx : t) : bool =
	let (overs, covers) = split ctx in
	let inner =
		List.fold_right
			(fun b acc -> Exists (b.name, b.sort, And (b.pred, acc)))
			covers True
	in
	valid (forall_overs overs inner)