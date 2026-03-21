%{
  open Assertion
  open Term
%}

%token <Z.t> NUM
%token <string> IDENT
%token LPAREN "("
%token RPAREN ")"
%token COMMA ","
%token AND "&"
%token OR "|"
%token NOT "~"
%token EQ "="
%token STAR "*"
%token COLON ":"
%token TRUE
%token FALSE EOF

%left OR
%left AND
%nonassoc NOT

%start <Assertion.expr> assertion
%start <Term.t> binding

%%

assertion:
  | e = prop; EOF { e }

binding:
  | v = term; EOF { v }

prop:
  | e1 = prop; "|"; e2 = prop { Or (e1, e2) }
  | e1 = prop; "&"; e2 = prop { And (e1, e2) }
  | "~"; e = prop { Not e }
  | "("; e = prop; ")" { e }
  | a = atom { Atom a }
  | TRUE { True }
  | FALSE { False }

atom:
  | lhs = term; "="; rhs = term { Cmp (lhs, Eq, rhs) }

term:
  | v = NUM { Const v }
  | tid = NUM; ":"; r = IDENT { LocVal (Reg (Z.to_int tid, r)) }
  | "*"; s = IDENT { Deref (Mem s) }
  | f = IDENT; "("; args = separated_list(",", term); ")" { Fn (f, args) }
  | f = IDENT; "("; kw = separated_nonempty_list(",", kw_arg); ")" { KwFn (f, kw) }
  | s = IDENT { LocVal (Mem s) }

kw_arg:
  | k = IDENT; "="; v = term { (k, v) }
