open Common

type id = string
type chan = string

type typ =
  | Num
  | Str
  | Fdesc
  | Chan

type expr =
  | Var    of id
  | NumLit of int
  | StrLit of string
  | Plus   of expr * expr

type when_cond =
  | Always
  | NumEq  of id * int
  | ChanEq of id * id

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

type msg_pat  = id msg
type msg_decl = typ msg
type msg_expr = expr msg

type cmd =
  | Send   of chan * msg_expr
  | Call   of id * expr * expr
  | Spawn  of id * id
  | Assign of id * expr

type prog =
  | Nop
  | Seq of cmd * prog

type cond_prog =
  { condition : when_cond
  ; program   : prog
  }

let mk_cond_prog c r =
  { condition = c
  ; program   = r
  } 

type handler =
  { trigger  : msg_pat
  ; responds : cond_prog list
  }

let mk_handler t r =
  { trigger  = t
  ; responds = r
  }

type kaction_pat =
  | KAP_Any
  | KAP_KSend of string
  | KAP_KRecv of string

type ktrace_pat =
  (* core *)
  | KTP_Emp
  | KTP_Act  of kaction_pat
  | KTP_NAct of kaction_pat
  | KTP_Alt  of ktrace_pat * ktrace_pat
  | KTP_And  of ktrace_pat * ktrace_pat
  | KTP_Cat  of ktrace_pat * ktrace_pat
  | KTP_Star of ktrace_pat
  (* sugar *)
  | KTP_Any
  | KTP_Opt    of ktrace_pat
  | KTP_Plus   of ktrace_pat
  | KTP_Class  of kaction_pat list
  | KTP_NClass of kaction_pat list
  | KTP_Not    of ktrace_pat

let rec dktp = function
  (* core - just recurse *)
  | KTP_Emp    -> KTP_Emp
  | KTP_Act  x -> KTP_Act  x
  | KTP_NAct x -> KTP_NAct x
  | KTP_Star p -> KTP_Star (dktp p)
  | KTP_Alt (p1, p2) -> KTP_Alt (dktp p1, dktp p2)
  | KTP_And (p1, p2) -> KTP_And (dktp p1, dktp p2)
  | KTP_Cat (p1, p2) -> KTP_Cat (dktp p1, dktp p2)
  (* desugar *)
  | KTP_Any ->
      KTP_Act KAP_Any
  | KTP_Opt p ->
      KTP_Alt (KTP_Emp, dktp p)
  | KTP_Plus p ->
      let p' = dktp p in
      KTP_Cat (p', KTP_Star p')
  | KTP_Class [] ->
      failwith "dktp: empty KTP_Class"
  | KTP_Class x::[] ->
      KTP_Act x
  | KTP_Class x::xs ->
      KTP_Alt (KTP_Act x, dktp (KTP_Class xs))
  | KTP_NClass [] ->
      failwith "dktp: empty KTP_NClass"
  | KTP_NClass x::[] ->
      KTP_NAct x
  | KTP_NClass x::xs ->
      KTP_And (KTP_NAct x, dktp (KTP_NClass xs))
  | KTP_Not (KTP_Not p) ->
      dktp p
  | KTP_Not p ->
      match dktp p with (
      | KTP_Emp -> dktp (
          KTP_Plus KTP_Any)
      | KTP_Act x -> dktp (
          KTP_Alt ( KTP_Emp
                  , KTP_Alt ( KTP_Cat (KTP_NAct x, KTP_Star KTP_Any)
                            , KTP_Cat (KTP_Act  x, KTP_Plus KTP_Any))))
      | KTP_NAct x -> dktp (
          KTP_Alt ( KTP_Emp
                  , KTP_Alt ( KTP_Cat (KTP_Act  x, KTP_Star KTP_Any)
                            , KTP_Cat (KTP_NAct x, KTP_Plus KTP_Any))))
      | KTP_Alt (p1, p2) -> dktp (
          KTP_And (KTP_Not p1, KTP_Not p2))
      | KTP_And (p1, p2) -> dktp (
          KTP_Alt (KTP_Not p1, KTP_Not p2))
      | KTP_Cat (p1, p2) -> dktp (
          KTP_Alt ( KTP_Cat (KTP_Not p1, KTP_Star KTP_Any)
                  , KTP_Cat (p1, KTP_Cat (KTP_Not p2, KTP_Star KTP_Any))))
      | _ ->
          failwith "dktp: KTP_Not recursive case still had sugar"
      )

let desugar_ktrace_pat = dktp

type prop =
  | ImmAfter  of string * string
  | ImmBefore of string * string
  | KTracePat of ktrace_pat

type component =
  string

type kernel =
  { constants  : (id * expr) list
  ; var_decls  : (id * typ) list
  ; components : (id * string) list
  ; msg_decls  : msg_decl list
  ; init       : prog
  ; exchange   : chan * ((component * handler list) list)
  ; props      : (id * prop) list
  }

let empty_kernel =
  { constants  = []
  ; var_decls  = []
  ; components = []
  ; msg_decls  = []
  ; init       = Nop
  ; exchange   = ("__xch__", [])
  ; props      = []
  }

let ck_kernel _ =
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
