%{
  open Common
  open Kernel

  let parse_error s =
    failwith (mkstr "Parse: error on line %d" !line)

  (* NOTE to get commas right, we special case empty arg lists *)
%}

%token STATE COMPONENTS MESSAGES INIT EXCHANGE NUM STR FDESC CALL SEND SPAWN WHEN
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
  | constants
    STATE                     LCURL var_decls     RCURL
    COMPONENTS                LCURL comp_decls    RCURL
    MESSAGES                  LCURL msg_decls     RCURL
    INIT                      LCURL prog          RCURL
    EXCHANGE LPAREN ID RPAREN LCURL comp_handlers RCURL
    EOF
    { mk_kernel $1 $4 $8 $12 $16 ($20, $23) }
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
    { [(mk_cond_prog None $2)] }
  | WHEN LPAREN when_cond RPAREN LCURL prog RCURL cond_progs
    { (mk_cond_prog (Some $3) $6) :: $8 }
;;

cmd :
  | ID EQ CALL LPAREN expr COMMA expr RPAREN
    { Call ($1, $5, $7) }
  | SEND LPAREN ID COMMA msg_expr RPAREN
    { Send ($3, $5) }
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
  | ID EQUALITY NUMLIT { LogEq($1, $3) }
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
;;

comp_handlers :
  | /* empty */
    { [] }
  | comp_handler comp_handlers
    { $1 :: $2 }

comp_handler :
  | ID LCURL handlers RCURL
    { ($1, $3) }
