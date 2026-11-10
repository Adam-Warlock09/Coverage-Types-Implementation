let run (script : string) : string = 
	let (from_z3, to_z3) = Unix.open_process "z3 -in" in
	output_string to_z3 script;
	close_out to_z3;
	let answer = try input_line from_z3 with End_of_file -> "unknown" in
	ignore (Unix.close_process (from_z3, to_z3));
	String.trim answer

let valid ~(vars : (string * string) list) (formula : string) : bool =
	let decls =
		vars
		|> List.map (fun (name, sort) -> Printf.sprintf "(declare-const %s %s)" name sort)
		|> String.concat "\n"
	in
	let script = Printf.sprintf "%s\n(assert (not %s))\n(check-sat)\n" decls formula in
	run script = "unsat"