%{
  open Common
  open Spec

  let parse_error s =
    failwith (mkstr "Parse: error on line %d" !line)

  (* NOTE to get commas right, we special case empty arg lists *)
%}

%token MESSAGES PROTOCOL NUM STR FDESC CALL
%token SENDS RECVS EQ LCURL RCURL LPAREN RPAREN
%token COMMA SEMI EOF

%token <int> NUMLIT
%token <string> STRLIT
%token <string> ID

%start spec
%type <Spec.spec> spec

%%

spec :
  | MESSAGES LCURL msg_decls RCURL 
    PROTOCOL LCURL handlers RCURL
    EOF
    { spec $3 $7 }
;;

handlers :
  | handler
    { $1 :: [] }
  | handler handlers
    { $1 :: $2 }
;;

handler :
  | ID SENDS msg_pat
    LCURL prog RCURL
    { handler ($1, $3) $5 }
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
  | ID RECVS msg_expr SEMI
    { Send ($1, $3) }
;;

msg_expr :
  | ID LPAREN RPAREN
    { msg $1 [] }
  | ID LPAREN exprs RPAREN
    { msg $1 $3 }
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
    { msg $1 [] }
  | ID LPAREN ids RPAREN
    { msg $1 $3 }
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
    { msg $1 [] }
  | ID LPAREN typs RPAREN SEMI
    { msg $1 $3 }
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
