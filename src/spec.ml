type id =
  string

type chan =
  string

type typ =
  | Num
  | Str

type expr =
  | NLit of int
  | SLit of string
  | Var  of id

type 'a msg =
  { tag : string
  ; payload : 'a list
  }

let msg t p =
  { tag = t
  ; payload = p
  }

type msg_pat = id msg
type msg_decl = typ msg
type msg_expr = expr msg

type prog =
  | Send of chan * msg_expr
  | Seq of prog * prog

type handler =
  { trigger : chan * msg_pat
  ; respond : prog
  }

let handler t r =
  { trigger = t
  ; respond = r
  }

type spec =
  { msg_decl : msg_decl list
  ; protocol : handler list
  }

let spec m p =
  { msg_decl = m
  ; protocol = p
  }

(* support lex/parse error reporting *)
let line =
  ref 1
