%{
  open Assertion
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
%token TRUE
%token FALSE EOF

%left OR
%left AND
%nonassoc NOT

%start <Assertion.expr> final_expr

%%

final_expr:
  | e = expr; EOF { e }

expr:
  | e1 = expr; "|"; e2 = expr { Or (e1, e2) }
  | e1 = expr; "&"; e2 = expr { And (e1, e2) }
  | "~"; e = expr { Not e }
  | "("; e = expr; ")" { e }
  | a = atom { Atom a }
  | TRUE { True }
  | FALSE { False }

atom:
  | l = loc; "="; v = NUM {
      match l with
      | Reg _ -> CmpCst (l, Eq, v)
      | Mem _ -> failwith "assertion: use *sym = value for memory comparisons"
    }
  | l1 = loc; "="; l2 = loc { CmpLoc (l1, Eq, l2) }
  | "*"; s = IDENT; "="; v = NUM { CmpCst (Mem s, Eq, v) }

loc:
  | tid = NUM; ":"; r = IDENT { Reg (Z.to_int tid, r) }
  | s = IDENT { Mem s }
