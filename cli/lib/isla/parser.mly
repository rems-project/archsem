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

%start <Assertion.expr> assertion

%%

assertion:
  | e = prop; EOF { e }

prop:
  | e1 = prop; "|"; e2 = prop { Or (e1, e2) }
  | e1 = prop; "&"; e2 = prop { And (e1, e2) }
  | "~"; e = prop { Not e }
  | "("; e = prop; ")" { e }
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
