%{
  open Ast
%}

%token <Z.t> NUM
%token <string> IDENT
%token LPAREN "("
%token RPAREN ")"
%token AND "&"
%token OR "|"
%token NOT "~"
%token EQ "="
%token STAR "*"
%token COLON ":"
%token TRUE EOF

%left OR
%left AND
%nonassoc NOT

%start <Ast.expr> expr_eof

%%

expr_eof:
  | e = expr; EOF { e }

expr:
  | e1 = expr; "|"; e2 = expr         { Or (e1, e2) }
  | e1 = expr; "&"; e2 = expr         { And (e1, e2) }
  | "~"; e = expr                     { Not e }
  | "("; e = expr; ")"                { e }
  | tid = NUM; ":"; r = IDENT; "="; v = NUM
    { Atom (RegEq (Z.to_int tid, r, v)) }
  | "*"; s = IDENT; "="; v = NUM     { Atom (MemEq (s, v)) }
  | TRUE                              { True }
