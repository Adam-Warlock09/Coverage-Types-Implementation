{
open Parser

exception Lex_error of string
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z' '_']
(* no apostrophes in names: Z3 would reject them *)
let ident = alpha (alpha | digit)*

rule token = parse
	| [' ' '\t']+     { token lexbuf }
	| '\n' | "\r\n"   { Lexing.new_line lexbuf; token lexbuf }
	| "(*"            { comment 1 lexbuf }

	| "()"            { UNIT }

	(* keywords: listed before ident, so "let" is LET but "letter" is IDENT *)
	| "let"           { LET }
	| "in"            { IN }
	| "if"            { IF }
	| "then"          { THEN }
	| "else"          { ELSE }
	| "true"          { TRUE }
	| "false"         { FALSE }
	| "err"           { ERR }
	| "not"           { NOT }
	| "mod"           { MOD }
	| "int"           { TINT }
	| "bool"          { TBOOL }

	(* longer symbols first is not required (ocamllex takes the longest match),
	   but it reads better *)
	| "==>"           { IMPLIES }
	| "<=>"           { IFF }
	| "=="            { EQEQ }
	| "<>"            { NEQ }
	| "!="            { NEQ }
	| "<="            { LEQ }
	| ">="            { GEQ }
	| "&&"            { AND }
	| "||"            { OR }
	| "="             { EQ }
	| "<"             { LT }
	| ">"             { GT }
	| "+"             { PLUS }
	| "-"             { MINUS }
	| "*"             { STAR }
	| "("             { LPAREN }
	| ")"             { RPAREN }
	| "{"             { LBRACE }
	| "}"             { RBRACE }
	| "["             { LBRACK }
	| "]"             { RBRACK }
	| ":"             { COLON }
	| "|"             { BAR }

	| digit+ as n     { INT (int_of_string n) }
	| ident as x      { IDENT x }
	| eof             { EOF }
	| _ as c          { raise (Lex_error (Printf.sprintf "unexpected character '%c'" c)) }

(* nested comments, as in your Liquid lexer *)
and comment depth = parse
	| "(*"            { comment (depth + 1) lexbuf }
	| "*)"            { if depth = 1 then token lexbuf else comment (depth - 1) lexbuf }
	| '\n'            { Lexing.new_line lexbuf; comment depth lexbuf }
	| eof             { raise (Lex_error "unterminated comment") }
	| _               { comment depth lexbuf }