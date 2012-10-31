open Common
open Kernel
open Gen

let py_recv_typ = function
  | Num   -> "recv_num"
  | Str   -> "recv_str"
  | Fdesc -> "recv_fd"
  | Chan  -> "recv_fd"

let py_send_typ = function
  | Num   -> "send_num"
  | Str   -> "send_str"
  | Fdesc -> "send_fd"
  | Chan  -> "send_fd"

let py_recv_msg tag_map m =
  let args =
    m.payload
      |> List.map (fun t -> mkstr "%s()" (py_recv_typ t))
      |> String.concat ", "
  in
  mkstr "%d : lambda _ : ['%s', %s],"
    (List.assoc m.tag tag_map) m.tag args

let py_send_msg tag_map m =
  let args =
    m.payload
      |> mapi (fun i t -> mkstr "%s(m[%d])" (py_send_typ t) (i + 1))
      |> String.concat ", "
  in
  mkstr "'%s' : lambda _ : [send_num(%d), %s],"
    m.tag (List.assoc m.tag tag_map) args

let subs k =
  let tm = gen_tag_map k in
  List.map (fun (f, r) -> (Str.regexp f, r))
  [ "__RECV_CASES__",
      fmt k.msg_decls (py_recv_msg tm)
  ; "__SEND_CASES__",
      fmt k.msg_decls (py_send_msg tm)
  ]
