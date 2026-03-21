%{
  open Pgtable
%}

%token <Z.t> NUM
%token <string> IDENT
%token LPAREN "("
%token RPAREN ")"
%token LBRACKET "["
%token RBRACKET "]"
%token LBRACE "{"
%token RBRACE "}"
%token COMMA ","
%token SEMICOLON ";"
%token EQ "="
%token STAR "*"
%token MAPS_TO "|->"
%token OPT_MAPS_TO "?->"
%token PHYSICAL VIRTUAL INTERMEDIATE ALIGNED
%token IDENTITY INVALID WITH AT LEVEL AS DEFAULT CODE AND_KW
%token S1TABLE S2TABLE OPTION TRUE FALSE
%token ASSERT
%token EQEQ "=="
%token BANGEQ "!="
%token DOTDOT ".."
%token EOF

%start <Pgtable.stmt list> program

%%

program:
  | stmts = list(stmt); EOF { stmts }

stmt:
  | d = addr_decl; ";"  { AddrDecl d }
  | m = mapping; ";"    { m }
  | m = opt_mapping; ";" { m }
  | i = identity; ";"   { i }
  | m = mem_init; ";"   { m }
  | t = table_block; ";"? { t }
  | t = table_ref; ";"  { t }
  | o = option_stmt; ";" { o }
  | a = assert_stmt; ";" { a }

addr_decl:
  | k = addr_kind; names = nonempty_list(IDENT)
    { { kind = k; names; alignment = None } }
  | ALIGNED; n = NUM; k = addr_kind; names = nonempty_list(IDENT)
    { { kind = k; names; alignment = Some (Z.to_int n) } }

addr_kind:
  | PHYSICAL     { Physical }
  | VIRTUAL      { Virtual }
  | INTERMEDIATE { Intermediate }

mapping_target:
  | name = IDENT { PA name }
  | INVALID      { Invalid }
  | f = IDENT; "("; _args = separated_list(",", value_expr); ")"
    { PA f }  (* function-call targets like table(addr): treat as PA for parsing *)

mapping_source:
  | f = IDENT; "("; args = separated_list(",", value_expr); ")"
    { SrcExpr (Term.Fn (f, args)) }
  | name = IDENT { SrcName name }

mapping:
  | va = mapping_source; "|->"; pa = mapping_target; m = mapping_mods
    { Mapping { va; pa; modifiers = m } }

opt_mapping:
  | va = mapping_source; "?->"; pa = mapping_target; m = mapping_mods
    { OptMapping { va; pa; modifiers = m } }

mapping_mods:
  | (* empty *)                         { no_mod }
  | WITH; w = with_spec; t = mapping_tail
    { { t with with_spec = w } }
  | AT; LEVEL; n = NUM; t = mapping_tail
    { { t with level = Some (Z.to_int n) } }
  | AS; name = IDENT; t = mapping_tail
    { { t with walk_name = Some name } }

mapping_tail:
  | (* empty *)                         { no_mod }
  | AT; LEVEL; n = NUM; t = mapping_tail
    { { t with level = Some (Z.to_int n) } }
  | AS; name = IDENT; t = mapping_tail
    { { t with walk_name = Some name } }

with_spec:
  | items = separated_nonempty_list(AND_KW, with_spec_item) { items }

with_spec_item:
  | DEFAULT { WsDefault }
  | CODE    { WsCode }
  | g = attr_group { WsAttrs g }

attr_group:
  | "["; attrs = separated_nonempty_list(",", attr); "]" { attrs }

attr:
  | name = IDENT; "="; v = value_expr { (name, v) }

identity_target:
  | f = IDENT; "("; args = separated_list(",", value_expr); ")"
    { IdFn (f, args) }
  | name = IDENT { IdName name }
  | addr = NUM   { IdAddr (Z.to_int addr) }

identity:
  | IDENTITY; t = identity_target
    { Identity { target = t; with_spec = [WsDefault] } }
  | IDENTITY; t = identity_target; WITH; w = with_spec
    { Identity { target = t; with_spec = w } }

mem_init:
  | "*"; addr = IDENT; "="; v = value_expr
    { MemInit { addr; value = v } }

table_stage:
  | S1TABLE { Pgtable.S1 }
  | S2TABLE { Pgtable.S2 }

table_block:
  | s = table_stage; name = IDENT; base = NUM;
    "{"; body = list(stmt); "}"
    { TableBlock { stage = s; name; base = Z.to_int base; body } }

table_ref:
  | s = table_stage; name = IDENT
    { TableRef { stage = s; name } }

option_stmt:
  | OPTION; name = IDENT; "="; TRUE  { Option { name; value = true } }
  | OPTION; name = IDENT; "="; FALSE { Option { name; value = false } }

value_expr:
  | v = NUM { Term.Const v }
  | f = IDENT; "("; args = separated_list(",", value_expr); ")"
    { Term.Fn (f, args) }
  | s = IDENT { Term.LocVal (Mem s) }

assert_stmt:
  | ASSERT; l = assert_expr; op = cmp_op; r = assert_expr
    { Assert { lhs = l; op; rhs = r } }

cmp_op:
  | EQEQ   { CmpEq }
  | BANGEQ { CmpNeq }

assert_expr:
  | name = IDENT; "["; hi = NUM; ".."; lo = NUM; "]"
    { ASlice (name, Z.to_int hi, Z.to_int lo) }
  | f = IDENT; "("; args = separated_list(",", assert_expr); ")"
    { AFn (f, args) }
  | n = NUM { AFn (Z.to_string n, []) }
  | name = IDENT { AVar name }
