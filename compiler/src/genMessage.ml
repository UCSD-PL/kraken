open Common
open Kernel
open Gen

let coq_recv_typ = function
  | Num   -> "recv_num", "RecvNum"
  | Str   -> "recv_str", "RecvStr"
  | Fdesc -> "recv_fd",  "RecvFD_t"
  | Chan  -> "recv_fd",  "RecvChan_t"

let coq_send_typ = function
  | Num   -> "send_num", "SendNum"
  | Str   -> "send_str", "SendStr"
  | Fdesc -> "send_fd",  "SendFD_t"
  | Chan  -> "send_fd",  "SendChan_t"

let coq_of_constant_decl (id, e) =
  lcat
    [ mkstr "Definition %s := %s." id (coq_of_expr e)
    ; mkstr "Global Opaque %s." id
    ]

let coq_of_msg_decl m =
  mkstr "| %s : %s" m.tag
    (m.payload
      |> List.map coq_of_typ
      |> List.map (mkstr "%s -> ")
      |> String.concat ""
      |> mkstr "%smsg")

let coq_trace_recv_msg tag_map m =
  let hdr =
    mkstr "| %s %s =>" m.tag (coq_of_args m)
  in
  let pay =
    if m.payload = [] then
      "(* empty payload *)"
    else
      m.payload
        |> mapi (fun i t ->
            let _, rT = coq_recv_typ t in
            mkstr "%s c p%d ++" rT i)
        |> List.rev
        |> lcat
  in
  let tag =
    mkstr "RecvNum c %s"
      (coq_num_of_int (List.assoc m.tag tag_map))
  in
  lcat [hdr; pay; tag]

(* WARNING copy/paste of coq_trace_recv_msg *)
let coq_trace_send_msg tag_map m =
  let hdr =
    mkstr "| %s %s =>" m.tag (coq_of_args m)
  in
  let pay =
    if m.payload = [] then
      "(* empty payload *)"
    else
      m.payload
        |> mapi (fun i t ->
            let _, sT = coq_send_typ t in
            mkstr "%s c p%d ++" sT i)
        |> List.rev
        |> lcat
  in
  let tag =
    mkstr "SendNum c %s"
      (coq_num_of_int (List.assoc m.tag tag_map))
  in
  lcat [hdr; pay; tag]

(* recv msg on bound chan "c" *)
let coq_recv_msg tag_map m =
  let hdr =
    mkstr "| %s => (* %s *)"
      (coq_num_of_int (List.assoc m.tag tag_map)) m.tag
  in
  let pay =
    let aux (i, code, tr) t =
      let rF, rT = coq_recv_typ t in
      ( i + 1
      , mkstr "p%d <- %s c\n(tr ~~~ %s);" i rF tr :: code
      , mkstr "%s c p%d ++ %s" rT i tr
      )
    in
    let tr =
      mkstr "RecvNum c %s ++ tr"
        (coq_num_of_int (List.assoc m.tag tag_map))
    in
    m.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
      |> List.rev
      |> lcat
  in
  let ret =
    mkstr "{{ Return (%s %s) }}\n" m.tag (coq_of_args m)
  in
  lcat [hdr; pay; ret]

(* send msg on bound chan "c" *)
(* WARNING copy/paste of coq_recv_msg *)
let coq_send_msg tag_map m =
  let hdr = lcat
    [ mkstr "| %s %s =>" m.tag (coq_of_args m)
    ; mkstr "send_num c %s tr;;" (coq_num_of_int (List.assoc m.tag tag_map))
    ]
  in
  let pay =
    let aux (i, code, tr) t =
      let sF, sT = coq_send_typ t in
      ( i + 1
      , mkstr "%s c p%d\n(tr ~~~ %s);;" sF i tr :: code
      , mkstr "%s c p%d ++ %s" sT i tr
      )
    in
    let tr =
      mkstr "SendNum c %s ++ tr"
        (coq_num_of_int (List.assoc m.tag tag_map))
    in
    m.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
      |> List.rev
      |> lcat
  in
  let ret =
    "{{ Return tt }}"
  in
  lcat [hdr; pay; ret]

let subs k =
  let tm = gen_tag_map k in
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "CONST_DECLS",
      fmt k.constants coq_of_constant_decl
  ; "COMP_DECLS",
      fmt k.components (fun (id, _) -> "| " ^ id)
  ; "CHAN_PATHS",
      fmt k.components (fun (id, path) ->
        mkstr "  | %s => str_of_string \"%s\"" id path)
  ; "MSG_DECL",
      fmt k.msg_decls coq_of_msg_decl
  ; "RECV_T_CASES",
      fmt k.msg_decls (coq_trace_recv_msg tm)
  ; "SEND_T_CASES",
      fmt k.msg_decls (coq_trace_send_msg tm)
  ; "RECV_CASES",
      fmt k.msg_decls (coq_recv_msg tm)
  ; "SEND_CASES",
      fmt k.msg_decls (coq_send_msg tm)
  ]
