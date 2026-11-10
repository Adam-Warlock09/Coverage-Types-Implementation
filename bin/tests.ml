open Coverage
open Formula
open Expr

module R = Rtype
module T = Typecheck

let v = Var "v"
let ints phi = R.RCover (SInt, phi)
let even x = Eq (Mod (x, Num 2), Num 0)

let odd x = Eq (Mod (x, Num 2), Num 1)

let run ?(params = []) name prog target expected =
	Printf.printf "%s\n" name;
	List.iter (fun (x, ty) -> Printf.printf "  param:   %s : %s\n" x (R.show ty)) params;
	Printf.printf "  program: %s\n" (show prog);
	Printf.printf "  target:  %s\n" (R.show target);
	let ctx = T.context_of_params params in
	let got =
		try T.check ctx prog target
		with T.Type_error msg -> (Printf.printf "  type error: %s\n" msg; false)
	in
	Printf.printf "  result:  %b   (expected %b)%s\n\n" got expected
		(if got = expected then "" else "   <-- MISMATCH")

(* ---------- Programs ---------- *)

(* let n = int_gen () in let m = n mod 2 in let b = m == 0 in if b then n else err *)
let even_gen =
	Let ("n", Gen SInt,
	Let ("m", Prim (Modulo, AVar "n", AInt 2),
	Let ("b", Prim (Equal, AVar "m", AInt 0),
	If (AVar "b", Atom (AVar "n"), Err SInt))))

(* same, branches swapped (the paper's Example 6.1 as printed) *)
let even_gen_swapped =
	Let ("n", Gen SInt,
	Let ("m", Prim (Modulo, AVar "n", AInt 2),
	Let ("b", Prim (Equal, AVar "m", AInt 0),
	If (AVar "b", Err SInt, Atom (AVar "n")))))

(* let c = bool_gen () in if c then 1 else 2 *)
let one_or_two =
	Let ("c", Gen SBool, If (AVar "c", Atom (AInt 1), Atom (AInt 2)))

(* Generate an int between lo and hi.
   cmp is the first comparison: LessEq is correct, Less is an off-by-one bug.
     let x = int_gen () in
     let c1 = lo <cmp> x in
     if c1 then (let c2 = x <= hi in if c2 then x else err) else err *)
let interval cmp =
	Let ("x", Gen SInt,
	Let ("c1", Prim (cmp, AVar "lo", AVar "x"),
	If (AVar "c1",
		Let ("c2", Prim (LessEq, AVar "x", AVar "hi"),
		If (AVar "c2", Atom (AVar "x"), Err SInt)),
		Err SInt)))

(* lo : {v | true},  hi : {v | v >= lo}   (both chosen by the caller) *)
let interval_params =
	[ ("lo", R.ROver (SInt, True));
	  ("hi", R.ROver (SInt, Ge (v, Var "lo"))) ]

let in_range = ints (And (Le (Var "lo", v), Le (v, Var "hi")))

(* ---------- Tests ---------- *)

let () =
	print_endline "=== Table 1 from the paper ===\n";
	run "constant 1, covers [v = 1]?" (Atom (AInt 1)) (ints (Eq (v, Num 1))) true;
	run "constant 1, covers [v = 1 or v = 2]?" (Atom (AInt 1))
		(ints (Or (Eq (v, Num 1), Eq (v, Num 2)))) false;
	run "err, covers [v | false]?" (Err SInt) (ints False) true;
	run "err, covers [v = 1]?" (Err SInt) (ints (Eq (v, Num 1))) false;
	run "int_gen (), covers every int?" (Gen SInt) (ints True) true;

	print_endline "=== Random choice ===\n";
	run "one_or_two, covers [v = 1 or v = 2]?" one_or_two
		(ints (Or (Eq (v, Num 1), Eq (v, Num 2)))) true;
	run "one_or_two, covers every int?" one_or_two (ints True) false;

	print_endline "=== Even generator ===\n";
	run "even_gen, covers all even numbers?" even_gen (ints (even v)) true;
	run "even_gen, covers every int?" even_gen (ints True) false;
	run "swapped branches, covers all odd numbers?" even_gen_swapped (ints (odd v)) true;

	print_endline "=== Interval generator (with caller parameters) ===\n";
	run ~params:interval_params "correct, covers [lo <= v <= hi]?"
		(interval LessEq) in_range true;
	run ~params:interval_params "off-by-one (lo < x), covers [lo <= v <= hi]?"
		(interval Less) in_range false;
	run ~params:interval_params "correct, covers everything >= lo?"
		(interval LessEq) (ints (Le (Var "lo", v))) false;

	print_endline "=== Errors ===\n";
	run "unbound variable z" (Atom (AVar "z")) (ints True) false

(* ================= Step 5: functions and application ================= *)

(* int_range : lo:{v | true} -> hi:{v | v >= lo} -> [v | lo <= v <= hi] *)
let int_range_ty =
	R.RArrow ("lo", R.ROver (SInt, True),
	R.RArrow ("hi", R.ROver (SInt, Ge (v, Var "lo")),
	ints (And (Le (Var "lo", v), Le (v, Var "hi")))))

(* low:{v | true} -> [v | ...] *)
let from_low phi = R.RArrow ("low", R.ROver (SInt, True), ints phi)

(* (definition, expected result) *)
let defs =
	[ (* Step 4's interval generator, now as a named function *)
	  ({ T.name = "int_range"; ty = int_range_ty; body = interval LessEq }, true);

	  (* the off-by-one version, claiming the same type *)
	  ({ T.name = "int_range_buggy"; ty = int_range_ty; body = interval Less }, false);

	  (* paper Fig. 3 in miniature:
	     let high = int_gen () in int_range low high     covers every v >= low *)
	  ({ T.name = "at_least";
	     ty = from_low (Ge (v, Var "low"));
	     body = Let ("high", Gen SInt, App ("int_range", [ AVar "low"; AVar "high" ])) }, true);

	  (* arguments swapped: int_range high low  only reaches values <= low ... *)
	  ({ T.name = "at_least_swapped";
	     ty = from_low (Ge (v, Var "low"));
	     body = Let ("high", Gen SInt, App ("int_range", [ AVar "high"; AVar "low" ])) }, false);

	  (* ... so with the opposite target it is correct *)
	  ({ T.name = "at_most";
	     ty = from_low (Le (v, Var "low"));
	     body = Let ("high", Gen SInt, App ("int_range", [ AVar "high"; AVar "low" ])) }, true);

	  (* constant arguments, mixed with a branch:
	     let c = bool_gen () in if c then 1 else int_range 2 3 *)
	  ({ T.name = "one_to_three";
	     ty = ints (Or (Or (Eq (v, Num 1), Eq (v, Num 2)), Eq (v, Num 3)));
	     body = Let ("c", Gen SBool,
	                 If (AVar "c", Atom (AInt 1), App ("int_range", [ AInt 2; AInt 3 ]))) }, true);

	  (* breaks int_range's promise (hi >= lo), so the call guarantees nothing *)
	  ({ T.name = "bad_call";
	     ty = ints (Eq (v, Num 5));
	     body = App ("int_range", [ AInt 5; AInt 1 ]) }, false);

	  (* too few arguments: a type error *)
	  ({ T.name = "partial";
	     ty = ints True;
	     body = App ("int_range", [ AInt 1 ]) }, false) ]

let () =
	print_endline "=== Step 5: functions and application ===\n";
	let results = T.check_program (List.map fst defs) in
	List.iter2
		(fun (d, expected) (_, r) ->
			Printf.printf "%s : %s\n" d.T.name (R.show d.T.ty);
			Printf.printf "  body:   %s\n" (show d.T.body);
			let got =
				match r with
				| Ok b -> b
				| Error msg -> Printf.printf "  type error: %s\n" msg; false
			in
			Printf.printf "  result: %b   (expected %b)%s\n\n" got expected
				(if got = expected then "" else "   <-- MISMATCH"))
		defs results