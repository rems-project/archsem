%{
  open Assertion
  open Value_expr
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

%start <Assertion.expr> final_expr
%start <Value_expr.t> final_value_expr

%%

final_expr:
  | e = expr; EOF { e }

final_value_expr:
  | v = value_expr; EOF { v }

expr:
  | e1 = expr; "|"; e2 = expr { Or (e1, e2) }
  | e1 = expr; "&"; e2 = expr { And (e1, e2) }
  | "~"; e = expr { Not e }
  | "("; e = expr; ")" { e }
  | a = atom { Atom a }
  | TRUE { True }
  | FALSE { False }

atom:
  | lhs = value_expr; "="; rhs = value_expr { Cmp (lhs, Eq, rhs) }

value_expr:
  | v = NUM { Const v }
  | tid = NUM; ":"; r = IDENT { LocVal (Reg (Z.to_int tid, r)) }
  | "*"; s = IDENT { LocVal (Mem s) }
  | f = IDENT; "("; args = separated_list(",", value_expr); ")" { Fn (f, args) }
  | f = IDENT; "("; kw = separated_nonempty_list(",", kw_arg); ")" { KwFn (f, kw) }
  | s = IDENT { LocVal (Mem s) }

kw_arg:
  | k = IDENT; "="; v = value_expr { (k, v) }
