{
  open Common
  open Kernel
  open Parse

  let chop_quotes s =
    String.sub s 1 (String.length s - 2)
}

let num = "0" | ['1'-'9']['0'-'9']*
let str = '"'[^'"''\n']*'"'
let id = ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9']*
let comment = "#"[^'\n']*
let space = [' ' '\t']
let line = '\n'

rule token = parse
  | "HASCHANTYPE" { HASCHANTYPE }
  | "Constants" { CONSTANTS }
  | "State" { STATE }
  | "Components" { COMPONENTS }
  | "Messages" { MESSAGES }
  | "Init" { INIT }
  | "Exchange" { EXCHANGE }
  | "Properties" { PROPERTIES }
  | "when" { WHEN }
  | "num" { NUM }
  | "str" { STR }
  | "fdesc" { FDESC }
  | "chan" { CHAN }
  | "call" { CALL }
  | "send" { SEND }
  | "recv" { RECV }
  | "spawn" { SPAWN }
  | "ImmAfter" { IMMAFTER }
  | "ImmBefore" { IMMBEFORE }
  | "Match" { MATCH }
  | "=c"  { EQC }
  | "=n"  { EQN }
  | "!=c" { NEQC }
  | "!=n" { NEQN }
  | "="   { EQ }
  | "{"   { LCURL }
  | "}"   { RCURL }
  | "("   { LPAREN }
  | ")"   { RPAREN }
  | "["   { LSQUARE }
  | "]"   { RSQUARE }
  | "<<"  { LCTX }
  | ">>"  { RCTX }
  | ","   { COMMA }
  | ";"   { SEMI }
  | ":"   { COLON }
  | "+"   { PLUS }
  | "_"   { UNDER }
  | "!"   { BANG }
  | "^"   { CARET }
  | "."   { DOT }
  | "&"   { AMP }
  | "|"   { PIPE }
  | "?"   { OPT }
  | "*"   { STAR }
  | eof   { EOF }
  | num as x { NUMLIT (int_of_string x) }
  | str as x { STRLIT (chop_quotes x) }
  | id as x { ID x }
(* ignore *)
  | comment { token lexbuf }
  | space { token lexbuf }
  | line { Lexing.new_line lexbuf; token lexbuf }
(* error *)
  | _ as c { failwith
              (mkstr "Lex: bogus char '%c' on line %d"
                c lexbuf.Lexing.lex_curr_p.Lexing.pos_lnum) }
