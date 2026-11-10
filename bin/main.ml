open Coverage

module R = Rtype
module T = Typecheck

let read_file path = In_channel.with_open_text path In_channel.input_all

let parse_file path : Surface.def list =
	let lexbuf = Lexing.from_string (read_file path) in
	Lexing.set_filename lexbuf path;
	let error msg =
		let p = lexbuf.Lexing.lex_curr_p in
		Printf.eprintf "%s:%d:%d: %s\n" path p.pos_lnum (p.pos_cnum - p.pos_bol) msg;
		exit 1
	in
	try Parser.program Lexer.token lexbuf with
	| Lexer.Lex_error msg -> error msg
	| Parser.Error -> error "syntax error"

let () =
	let args = List.tl (Array.to_list Sys.argv) in
	let verbose = List.mem "-v" args in
	let path =
		match List.filter (fun a -> a <> "-v") args with
		| [ p ] -> p
		| _ -> prerr_endline "usage: main.exe [-v] FILE.cov"; exit 1
	in
	let elaborated = Elaborate.elaborate (parse_file path) in
	let covered = ref 0 in
	ignore
		(List.fold_left
			(fun fenv (name, line, r) ->
				Printf.printf "%s  (line %d)\n" name line;
				match r with
				| Error msg ->
					Printf.printf "  ERROR: %s\n\n" msg;
					fenv
				| Ok d ->
					if verbose then begin
						Printf.printf "  type: %s\n" (R.show d.T.ty);
						Printf.printf "  core: %s\n" (Expr.show d.T.body)
					end;
					let verdict =
						try if T.check_def fenv d then (incr covered; "covered") else "NOT covered"
						with T.Type_error msg -> "ERROR: " ^ msg
					in
					Printf.printf "  => %s\n\n" verdict;
					(d.T.name, d.T.ty) :: fenv)
			[] elaborated);
	Printf.printf "%d of %d definitions cover their type\n" !covered (List.length elaborated)