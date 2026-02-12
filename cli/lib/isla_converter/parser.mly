%{
open Ast
%}

/* Tokens */
%token <string> ID HEX INT BIN
%token KW_PHYSICAL KW_INTERMEDIATE KW_VIRTUAL KW_ALIGNED KW_OPTION
%token KW_S1TABLE KW_S2TABLE KW_TABLE KW_IDENTITY KW_ASSERT
%token KW_WITH KW_CODE KW_DEFAULT KW_INVALID KW_RAW
%token KW_AT KW_LEVEL KW_AS KW_AND
%token SEMI LBRACE RBRACE LPAREN RPAREN LBRACKET RBRACKET
%token COMMA EQ STAR ARROW VAR_ARROW
%token DOTDOT EQEQ NEQ
%token EOF

%start <Ast.stmt list> main_dsl
%start <Ast.expr> main_expr

%%

main_dsl:
  | stmts EOF { $1 }

stmts:
  | /* empty */ { [] }
  | stmt stmts  { $1 :: $2 }

stmt:
  | KW_PHYSICAL names SEMI      { Decl("physical", $2) }
  | KW_INTERMEDIATE names SEMI  { Decl("intermediate", $2) }
  | KW_VIRTUAL names SEMI       { Decl("virtual", $2) }
  | KW_ALIGNED INT KW_VIRTUAL names SEMI { Decl("virtual", $4) }
  | KW_OPTION ID EQ val_tok SEMI { OptionDef($2, $4) }
  | KW_ASSERT constr SEMI { Assert($2) }
  | KW_S1TABLE ID HEX LBRACE stmts RBRACE SEMI { TableDef{name=$2; addr=$3; body=$5} }
  | KW_S1TABLE ID HEX LBRACE stmts RBRACE { TableDef{name=$2; addr=$3; body=$5} }
  | KW_S2TABLE ID HEX LBRACE stmts RBRACE SEMI { TableDef{name=$2; addr=$3; body=$5} }
  | KW_S2TABLE ID HEX LBRACE stmts RBRACE { TableDef{name=$2; addr=$3; body=$5} }
  | KW_S1TABLE ID SEMI { Decl("table_ref", [$2]) }
  | KW_S2TABLE ID SEMI { Decl("table_ref", [$2]) }
  | KW_IDENTITY HEX attrs SEMI { Identity($2, $3) }
  | KW_IDENTITY ID LPAREN HEX RPAREN attrs SEMI { Identity($4, $6) }
  | STAR ID EQ INT SEMI { MemInit($2, $4) }
  | mapping_stmt { $1 }

mapping_stmt:
  | complex_lhs ARROW target alias_opt attrs level_opt SEMI
      { Mapping{va=$1; target=$3; variant=false; level=$6; alias=$4} }
  | complex_lhs VAR_ARROW target alias_opt attrs level_opt SEMI
      { Mapping{va=$1; target=$3; variant=true; level=$6; alias=$4} }

constr:
  | expr EQEQ expr { Eq($1, $3) }
  | expr NEQ expr { Neq($1, $3) }

complex_lhs:
  | ID { $1 }
  | func_call { $1 }

func_call:
  | ID LPAREN arg_list_str RPAREN { $1 ^ "(" ^ $3 ^ ")" }

arg_list_str:
  | /* empty */ { "" }
  | arg_items { $1 }

arg_items:
  | arg_str { $1 }
  | arg_str COMMA arg_items { $1 ^ "," ^ $3 }

arg_str:
  | ID { $1 }
  | HEX { $1 }
  | INT { $1 }
  | func_call { $1 }

names:
  | ID { [$1] }
  | names ID { $1 @ [$2] }
  | names COMMA ID { $1 @ [$3] }

val_tok:
  | INT { $1 }
  | ID  { "val" }

target:
  | ID { TPA($1) }
  | KW_INVALID { TInvalid }
  | KW_TABLE LPAREN ID RPAREN { TTable($3) } /* Now storing the ID string */
  | KW_TABLE LPAREN HEX RPAREN { TTableAddr(Z.of_string $3) }
  | KW_TABLE LPAREN INT RPAREN { TTableAddr(Z.of_string $3) }
  | KW_RAW LPAREN INT RPAREN { TRaw(Z.of_string $3) }

alias_opt:
  | /* empty */ { None }
  | KW_AS ID { Some($2) }

/* attrs now returns bool indicating is_code */
attrs:
  | /* empty */ { false }
  | KW_WITH attrs_content { $2 }

attrs_content:
  | KW_CODE { true }
  | KW_DEFAULT { false }
  | LBRACKET bracket_content RBRACKET { false }
  | attrs_content KW_AND KW_DEFAULT { $1 }

bracket_content:
  | ID EQ val_tok { () }
  | ID EQ HEX { () }
  | ID EQ BIN { () }
  | /* empty */ { () }

level_opt:
  | /* empty */ { None }
  | KW_AT KW_LEVEL INT { Some(int_of_string $3) }

/* --- Expression Parser --- */

main_expr:
  | expr EOF { $1 }

expr:
  | INT { EInt(Z.of_string $1) }
  | HEX { EInt(Z.of_string $1) }
  | BIN { EInt(Z.of_string $1) }
  | ID  { EVar($1) }
  | ID LPAREN args RPAREN { ECall($1, $3) }
  | expr LBRACKET INT DOTDOT INT RBRACKET { ESlice($1, int_of_string $3, int_of_string $5) }

args:
  | /* empty */ { [] }
  | arg_items_expr { $1 }

arg_items_expr:
  | arg_item { [$1] }
  | arg_item COMMA arg_items_expr { $1 :: $3 }

arg_item:
  | expr { ("", $1) }
  | ID EQ expr { ($1, $3) }
  | KW_TABLE EQ expr { ("table", $3) }
  | KW_DEFAULT EQ expr { ("default", $3) }
  | KW_LEVEL EQ expr { ("level", $3) }
