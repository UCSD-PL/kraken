open Common

type id = string
type chan = string

type typ =
  | Num
  | Str
  | Fdesc
  | Chan

type expr =
  | Var of id
  | NumLit of int
  | StrLit of string
  | Plus of expr * expr

type 'a msg =
  { tag : string
  ; payload : 'a list
  }

let mk_msg t p =
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
  | Call of id * expr * expr
  | Spawn of id * id
  | Assign of id * expr

type prog =
  | Nop
  | Seq of cmd * prog

type handler =
  { trigger : msg_pat
  ; respond : prog
  }

let mk_handler t r =
  { trigger = t
  ; respond = r
  }

type kernel =
  { constants  : (id * expr) list
  ; var_decls  : (id * typ) list
  ; components : (id * string) list
  ; msg_decls  : msg_decl list
  ; init       : prog
  ; exchange   : chan * ((string * handler list) list)
  }

let mk_kernel cs vs comps ms i xch =
  { constants  = cs
  ; var_decls  = vs
  ; components = comps
  ; msg_decls  = ms
  ; init       = i
  ; exchange   = xch
  }

let ck_kernel s =
  (* TODO *)
  (* msg tags start with uppercase *)
  (* msg tags uniq *)
  (* BadTag not in msg tags *)
  (* msg pat triggers have uniq ids *)
  ()

(* generate unique id # for each message tag *)
(* start at 1 so BadTag can always have id 0 *)
let gen_tag_map kernel =
  let tags = List.map tag kernel.msg_decls in
  List.combine tags (range 1 (List.length tags + 1))

(* support lex/parse error reporting *)
let line = ref 1
