{
  open Common
  open Spec
  open Parse
}

let num =
  "0" | ['1'-'9']['0'-'9']*

let str =
  '"'[^'"']*'"'

let id =
  ['a'-'z''A'-'Z']['a'-'z''A'-'Z''0'-'9']*

let comment =
  "#"[^'\n']*

let space =
  [' ' '\t']

let line =
  '\n'

rule token = parse
  | "Messages" { MESSAGES }
  | "Protocol" { PROTOCOL }
  | "num" { NUM }
  | "str" { STR }
  | ">>" { SENDS }
  | "<<" { RECVS }
  | "{" { LCURL }
  | "}" { RCURL }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "," { COMMA }
  | ";" { SEMI }
  | eof { EOF }
  | num as x { NLIT (int_of_string x) }
  | str as x { SLIT x }
  | id as x { ID x }
(* ignore *)
  | comment { token lexbuf }
  | space { token lexbuf }
  | line { incr line; token lexbuf }
(* error *)
  | _ as c
    { failwith (mkstr "Lex: bogus char '%c' on line %d" c !line) }
