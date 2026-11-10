%{
open Surface
%}

%token <int> INT
%token <string> IDENT
%token LET IN IF THEN ELSE TRUE FALSE ERR NOT MOD TINT TBOOL
%token EQ EQEQ NEQ LT GT LEQ GEQ AND OR IMPLIES IFF PLUS MINUS STAR
%token LPAREN RPAREN UNIT LBRACE RBRACE LBRACK RBRACK COLON BAR EOF

(* lowest to highest.
   IN / ELSE lowest: the body of a let / else-branch extends as far right as possible *)
%nonassoc IN ELSE
%right IMPLIES
%nonassoc IFF
%left OR
%left AND
%nonassoc NOT
%nonassoc EQ EQEQ NEQ LT GT LEQ GEQ
%left PLUS MINUS
%left STAR MOD

%start <Surface.def list> program

%%

(* A file is a list of definitions. *)
program:
	| ds = list(def); EOF { ds }

(* let name (x : {v:int | ...}) ... : [v:int | ...] = body *)
def:
	| LET; name = IDENT; ps = list(param); COLON; r = rty; EQ; body = expr
		{ { name; params = ps; result = r; body; line = $startpos.Lexing.pos_lnum } }

param:
	| LPAREN; x = IDENT; COLON; t = rty; RPAREN { (x, t) }

rty:
	| LBRACE; x = IDENT; COLON; s = sort; BAR; p = expr; RBRACE { TRef (KOver, x, s, p) }
	| LBRACK; x = IDENT; COLON; s = sort; BAR; p = expr; RBRACK { TRef (KCover, x, s, p) }

sort:
	| TINT  { Formula.SInt }
	| TBOOL { Formula.SBool }

expr:
	| e = app                                         { e }
	| LET; x = IDENT; EQ; e1 = expr; IN; e2 = expr    { ELet (x, e1, e2) }
	| IF; c = expr; THEN; a = expr; ELSE; b = expr    { EIf (c, a, b) }
	| NOT; e = expr                                   { ENot e }
	| a = expr; op = binop; b = expr                  { EBin (op, a, b) }

(* %inline lets each operator keep its own precedence from the table above *)
%inline binop:
	| PLUS    { BAdd }    | MINUS { BSub }    | STAR  { BMul }   | MOD   { BMod }
	| EQ      { BEq }     | EQEQ  { BEq }     | NEQ   { BNeq }
	| LT      { BLt }     | LEQ   { BLe }     | GT    { BGt }    | GEQ   { BGe }
	| AND     { BAnd }    | OR    { BOr }     | IMPLIES { BImplies } | IFF { BIff }

(* function calls: f (), or f followed by one or more simple arguments *)
app:
	| e = atomic                                      { e }
	| f = IDENT; UNIT                                 { ECall (f, []) }
	| f = IDENT; args = nonempty_list(atomic)         { ECall (f, args) }

atomic:
	| LPAREN; e = expr; RPAREN  { e }
	| x = IDENT                 { EVar x }
	| n = INT                   { EInt n }
	| TRUE                      { EBool true }
	| FALSE                     { EBool false }
	| ERR                       { EErr }