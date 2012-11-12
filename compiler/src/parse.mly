%{
  open Common
  open Kernel

  let parse_error _ =
    failwith (mkstr "Parse: error on line %d" !line)

  (* NOTE to get commas correct, we special case empty arg lists *)

  (* global kernel ref, support omitted and arbitrarily ordered sections *)
  let _K = ref empty_kernel
%}

%token CONSTANTS STATE COMPONENTS MESSAGES INIT EXCHANGE PROPERTIES
%token NUM STR FDESC CHAN CALL SEND RECV SPAWN WHEN
%token EQ EQC EQN EQS COMMA SEMI COLON
%token PLUS AT BANG CARET DOT AMP PIPE OPT STAR
%token IMMAFTER IMMBEFORE MATCH
%token LCURL RCURL LPAREN RPAREN LSQUARE RSQUARE EOF

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
    { _K := { !_K with init = ($3, []) } }
  | EXCHANGE LPAREN ID RPAREN LCURL comp_handlers RCURL
    { _K := { !_K with exchange = ($3, $6) } }
  | PROPERTIES LCURL props RCURL
    { _K := { !_K with props = $3 } }
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
    { [(mk_cond_prog Always ($2, []))] }
  | WHEN LPAREN when_cond RPAREN LCURL prog RCURL cond_progs
    { (mk_cond_prog $3 ($6, [])) :: $8 }
;;

cmd :
  | ID EQ CALL LPAREN expr COMMA expr RPAREN
    { Call ($1, $5, $7) }
  | SEND LPAREN ID COMMA msg_expr RPAREN
    { Send ($3, $5) }
  | ID EQ SPAWN LPAREN comp_constr RPAREN
    { Spawn ($1, $5) }
  | SPAWN LPAREN comp_constr RPAREN
    { Spawn (mkstr "c%d" (tock ()), $3) }
  | ID EQ expr
    { Assign ($1, $3) }
;;

comp_constr :
  | ID
    { ($1, []) }
  | ID LPAREN comp_fields RPAREN
    { ($1, $3) }

comp_fields :
  | /* empty */
    { [] }
  | expr
    { [$1] }
  | expr COMMA comp_fields
    { $1 :: $3 }
;;

msg_expr :
  | ID LPAREN opt_commasep_exprs RPAREN
    { mk_msg $1 $3 }
;;

opt_commasep_exprs :
  | /* empty */
    { [] }
  | commasep_exprs
    { $1 }

commasep_exprs :
  | expr
    { $1 :: [] }
  | expr COMMA commasep_exprs
    { $1 :: $3 }
;;

expr :
  | expr PLUS expr                  { Plus($1, $3) }
  | NUMLIT                          { NumLit $1 }
  | STRLIT                          { StrLit $1 }
  | ID                              { Var $1 }
  | ID LPAREN commasep_exprs RPAREN { FunCall($1, $3) }
  | ID AT ID                        { CompFld($1, $3) }
;;

when_cond :
  | ID EQN NUMLIT { NumEq($1, $3) }
  | ID EQC ID     { ChanEq($1, $3) }
  | expr EQS expr { StrEq($1, $3) }
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
    { ($1, ($2, [])) }
  | ID STRLIT LCURL var_decls RCURL
    { ($1, ($2, $4)) }
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
;;

comp_handler :
  | ID LCURL handlers RCURL
    { ($1, $3) }
;;

props :
  | /* empty */
    { [] }
  | ID EQ prop SEMI props
    { ($1, $3) :: $5 }
;;

prop :
  | IMMAFTER LCURL STRLIT RCURL LCURL STRLIT RCURL
    { ImmAfter ($3, $6) }
  | IMMBEFORE LCURL STRLIT RCURL LCURL STRLIT RCURL
    { ImmBefore ($3, $6) }
  | MATCH LCURL ktrace_spec RCURL
    { KTracePat $3 }
;;

kap :
  | SEND ID { KAP_KSend $2 }
  | RECV ID { KAP_KRecv $2 }
;;

pclass :
  | kap
    { KTP_Act $1 }
  | kap COMMA pclass
    { KTP_Alt (KTP_Act $1, $3) }
;;

nclass :
  | kap
    { KTP_NAct $1 }
  | kap COMMA nclass
    { KTP_And (KTP_NAct $1, $3) }
;;


/* TODO resolve conflicts w/ associativity and precedence annotations. */

ktp_00 :
  | DOT
    { KTP_Act KAP_Any }
  | LSQUARE pclass RSQUARE
    { $2 }
  | LSQUARE CARET nclass RSQUARE
    { $3 }
  | LPAREN ktrace_pat RPAREN
    { $2 }
;;

ktp_10 :
  | ktp_00
    { $1 }
  | ktp_10 OPT
    { KTP_Alt (KTP_Emp, $1) }
  | ktp_10 STAR
    { KTP_Star $1 }
  | ktp_10 PLUS
    { KTP_Cat ($1, KTP_Star $1) }
;;

ktp_20 :
  | ktp_10
    { $1 }
  | ktp_10 ktp_20
    { KTP_Cat ($1, $2) }
;;

ktp_25 :
  | ktp_20
    { $1 }
  | ktp_20 AMP ktp_25
    { KTP_And ($1, $3) }

ktp_30 :
  | ktp_25
    { $1 }
  | ktp_25 PIPE ktp_30
    { KTP_Alt ($1, $3) }
;;

ktrace_pat :
  | ktp_30 { $1 }
;;

ktrace_spec :
  | ktrace_pat      { KTS_Pat  $1 }
  | BANG ktrace_pat { KTS_NPat $2 }
;;
