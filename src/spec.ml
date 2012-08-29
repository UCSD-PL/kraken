open Common

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

let tag m =
  m.tag

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

(* sanity checks *)

let ckspec s =
  (* msg tags start with uppercase *)
  (* msg tags uniq *)
  (* BadTag not in msg tags *)
  ()

(* coq gen *)

let typ_coq = function
  | Num -> "num"
  | Str -> "str"

let msg_decl_coq mds =
  let fmt md =
    let ts =
      if md.payload = [] then
        "msg"
      else
        md.payload
          |> List.map typ_coq
          |> String.concat " -> "
          |> mkstr "%s -> msg"
    in
    mkstr "| %s : %s" md.tag ts
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Inductive msg : Set :=
%s
| BadTag : N -> msg.
"

let recv_msg_spec_coq tag_map mds =
  let fmt md =
    (* name each msg param *)
    let nms =
      md.payload
        |> List.length
        |> range 0
        |> List.map (mkstr "p%d")
    in
    let hdr =
      mkstr "    | %s %s =>" md.tag (String.concat " " nms)
    in
    let recv_typ = function
      | (Num, p) -> mkstr "      RecvNum c %s ++" p
      | (Str, p) -> mkstr "      RecvStr c %s ++" p
    in
    let recv_pay =
      List.combine md.payload nms
        |> List.rev
        |> List.map recv_typ
        |> String.concat "\n"
    in
    let recv_tag =
      mkstr "      RecvNum c %d"
        (List.assoc md.tag tag_map)
    in
    mkstr "%s\n%s\n%s"
      hdr recv_pay recv_tag
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition RecvMsg (c: chan) (m: msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      RecvNum c p0
  end.
"

(* WARNING : copy/paste of recv_msg_spec_coq *)
let send_msg_spec_coq tag_map mds =
  let fmt md =
    (* name each msg param *)
    let nms =
      md.payload
        |> List.length
        |> range 0
        |> List.map (mkstr "p%d")
    in
    let hdr =
      mkstr "    | %s %s =>" md.tag (String.concat " " nms)
    in
    let recv_typ = function
      | (Num, p) -> mkstr "      SendNum c %s ++" p
      | (Str, p) -> mkstr "      SendStr c %s ++" p
    in
    let recv_pay =
      List.combine md.payload nms
        |> List.rev
        |> List.map recv_typ
        |> String.concat "\n"
    in
    let recv_tag =
      mkstr "      SendNum c %d"
        (List.assoc md.tag tag_map)
    in
    mkstr "%s\n%s\n%s"
      hdr recv_pay recv_tag
  in
  mds
    |> List.map fmt
    |> String.concat "\n"
    |> mkstr "
Definition SendMsg (c: chan) (m: msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      SendNum c 0
  end.
"

let spec_coq s =
  let tag_map =
    let tags =
      List.map tag s.msg_decl
    in
    (* generate id number for each tag *)
    (* start at 1 so BadTag can always have id 0 *)
    let ids =
      tags
        |> List.length
        |> range 0
        |> List.map ((+) 1)
    in
    List.combine tags ids
  in
  mkstr "%s%s%s"
    (msg_decl_coq s.msg_decl)
    (recv_msg_spec_coq tag_map s.msg_decl)
    (send_msg_spec_coq tag_map s.msg_decl)

(* support lex/parse error reporting *)
let line =
  ref 1
