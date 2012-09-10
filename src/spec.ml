open Common

type id = string
type chan = string

type typ =
  | Num
  | Str
  | Fdesc

type expr =
  | NumLit of int
  | StrLit of string
  | Var of id

type 'a msg =
  { tag : string
  ; payload : 'a list
  }

let msg t p =
  { tag = t
  ; payload = p
  }

let tag m =
  m.tag

type msg_pat = id msg
type msg_decl = typ msg
type msg_expr = expr msg

type cmd =
  | Send of chan * msg_expr
  | Call of id * string * expr

type prog =
  | Nop
  | Seq of cmd * prog

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

let ckspec s =
  (* TODO *)
  (* msg tags start with uppercase *)
  (* msg tags uniq *)
  (* BadTag not in msg tags *)
  (* msg pat triggers have uniq ids *)
  ()

(* support lex/parse error reporting *)
let line = ref 1
