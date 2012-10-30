%{
  open Common
  open Kernel

  let parse_error s =
    failwith (mkstr "Parse: error on line %d" !line)

  (* NOTE to get commas correct, we special case empty arg lists *)

  (* global kernel ref, support omitted and arbitrarily ordered sections *)
  let _K = ref empty_kernel
%}

%token CONSTANTS STATE COMPONENTS MESSAGES INIT EXCHANGE WHEN
%token NUM STR FDESC CHAN CALL SEND SPAWN 
%token EQ EQUALITY LCURL RCURL LPAREN RPAREN
%token COMMA SEMI EOF COLON ASSIGN PLUS

%right PLUS

%token <int> NUMLIT
%token <string> STRLIT
%token <string> ID

%start kernel
%type <Kernel.kernel> kernel

%%

kernel :
  | section kernel
    { $2 }
  | EOF
    { !_K }
;;

/* overwrite repeat sections */
section :
  | CONSTANTS LCURL constants RCURL
    { _K := { !_K with constants = $3 } }
  | STATE LCURL var_decls RCURL
    { _K := { !_K with var_decls = $3 } }
  | COMPONENTS LCURL comp_decls RCURL
    { _K := { !_K with components = $3 } }
  | MESSAGES LCURL msg_decls RCURL
    { _K := { !_K with msg_decls = $3 } }
  | INIT LCURL prog RCURL
    { _K := { !_K with init = $3 } }
  | EXCHANGE LPAREN ID RPAREN LCURL comp_handlers RCURL
    { _K := { !_K with exchange = ($3, $6) } }
;;

constants :
  | /* empty */
    { [] }
  | ID EQ expr SEMI constants
    { ($1, $3) :: $5 }
;;

handlers :
  | /* empty */
    { [] }
  | handler handlers
    { $1 :: $2 }
;;

handler :
  | msg_pat cond_progs
    { mk_handler $1 $2 }
;;

prog :
  | /* empty */
    { Nop }
  | cmd SEMI prog
    { Seq ($1, $3) }
;;

cond_progs :
  | LCURL prog RCURL
    { [(mk_cond_prog Always $2)] }
  | WHEN LPAREN when_cond RPAREN LCURL prog RCURL cond_progs
    { (mk_cond_prog $3 $6) :: $8 }
;;

cmd :
  | ID ASSIGN CALL LPAREN expr COMMA expr RPAREN
    { Call ($1, $5, $7) }
  | SEND LPAREN ID COMMA msg_expr RPAREN
    { Send ($3, $5) }
  | ID ASSIGN SPAWN LPAREN ID RPAREN
    { Spawn ($1, $5) }
  | SPAWN LPAREN ID RPAREN
    { Spawn (mkstr "c%d" (tock ()), $3) }
  | ID ASSIGN expr
    { Assign ($1, $3) }
;;

msg_expr :
  | ID LPAREN RPAREN
    { mk_msg $1 [] }
  | ID LPAREN exprs RPAREN
    { mk_msg $1 $3 }
;;

exprs :
  | expr
    { $1 :: [] }
  | expr COMMA exprs
    { $1 :: $3 }
;;

expr :
  | expr PLUS expr { Plus($1, $3) }
  | NUMLIT { NumLit $1 }
  | STRLIT { StrLit $1 }
  | ID { Var $1 }
;;

when_cond :
  | ID EQUALITY NUMLIT { NumEq($1, $3) }
;;

msg_pat :
  | ID LPAREN RPAREN
    { mk_msg $1 [] }
  | ID LPAREN ids RPAREN
    { mk_msg $1 $3 }
;;

ids :
  | ID
    { $1 :: [] }
  | ID COMMA ids
    { $1 :: $3 }
;;

msg_decls :
  | msg_decl
    { $1 :: [] }
  | msg_decl msg_decls
    { $1 :: $2 }
;;

msg_decl :
  | ID LPAREN RPAREN SEMI
    { mk_msg $1 [] }
  | ID LPAREN typs RPAREN SEMI
    { mk_msg $1 $3 }
;;

var_decls :
  | /* empty */
    { [] }
  | var_decl var_decls
    { $1 :: $2 }
;;

var_decl :
  | ID COLON typ SEMI
    { ($1, $3) }
;;

comp_decls :
  | /* empty */
    { [] }
  | comp_decl comp_decls
    { $1 :: $2 }
;;

comp_decl :
  | ID STRLIT SEMI
    { ($1, $2) }
;;

typs :
  | typ
    { $1 :: [] }
  | typ COMMA typs
    { $1 :: $3 }
;;

typ :
  | NUM { Num }
  | STR { Str }
  | FDESC { Fdesc }
  | CHAN { Chan }
;;

comp_handlers :
  | /* empty */
    { [] }
  | comp_handler comp_handlers
    { $1 :: $2 }

comp_handler :
  | ID LCURL handlers RCURL
    { ($1, $3) }
