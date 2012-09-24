%{
  open Common
  open Kernel

  let parse_error s =
    failwith (mkstr "Parse: error on line %d" !line)

  (* NOTE to get commas right, we special case empty arg lists *)
%}

%token MESSAGES EXCHANGE NUM STR FDESC CALL SEND
%token EQ LCURL RCURL LPAREN RPAREN
%token COMMA SEMI EOF

%token <int> NUMLIT
%token <string> STRLIT
%token <string> ID

%start kernel
%type <Kernel.kernel> kernel

%%

kernel :
  | MESSAGES LCURL msg_decls RCURL 
    EXCHANGE LPAREN ID RPAREN LCURL handlers RCURL
    EOF
    { mk_kernel $3 ($7, $10) }
;;

handlers :
  | /* empty */
    { [] }
  | handler handlers
    { $1 :: $2 }
;;

handler :
  | msg_pat LCURL prog RCURL
    { mk_handler $1 $3 }
;;

prog :
  | /* empty */
    { Nop }
  | cmd prog
    { Seq ($1, $2) }
;;

cmd :
  | ID EQ CALL LPAREN STRLIT COMMA expr RPAREN SEMI
    { Call ($1, $5, $7) }
  | SEND LPAREN ID COMMA msg_expr RPAREN SEMI
    { Send ($3, $5) }
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
  | NUMLIT { NumLit $1 }
  | STRLIT { StrLit $1 }
  | ID { Var $1 }
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
