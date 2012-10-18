open Common
open Kernel

let fmt l f =
  l |> List.map f
    |> List.filter ((<>) "")
    |> String.concat "\n"

let c_mtyp tag_map m =
  mkstr "  MTYP_%s = %d,"
    m.tag (List.assoc m.tag tag_map)

let c_mtyp_str m =
  String.concat "\n"
    [ mkstr "    case MTYP_%s:" m.tag
    ; mkstr "      return strdup(\"%s\");" m.tag
    ]

let c_typ = function
  | Num -> "uint32_t"
  | Str -> "pstr *"
  | Fdesc -> "int"

let c_ptyp = function
  | Num -> "PTYP_NUM"
  | Str -> "PTYP_STR"
  | Fdesc -> "PTYP_FD"

let c_mk_param_typ = function
  | Num -> "mk_num_param"
  | Str -> "mk_pstr_param"
  | Fdesc -> "mk_fd_param"

let c_msg_ctor_proto m =
  let args =
    m.payload
      |> mapi (fun i t -> mkstr "%s p%d" (c_typ t) i)
      |> String.concat ", "
  in
  mkstr "msg * mk_%s_msg(%s);" m.tag args

let c_msg_ctor m =
  let args =
    m.payload
      |> mapi (fun i t -> mkstr "%s p%d" (c_typ t) i)
      |> String.concat ", "
  in
  (* foldr for this is just too ugly *)
  let pay =
    let rec loop i = function
      | [] -> "NULL"
      | t::ts -> mkstr "%s(p%d, %s)" (c_mk_param_typ t) i (loop (i+1) ts)
    in
    loop 0 m.payload
  in
  String.concat "\n"
    [       "msg *"
    ; mkstr "mk_%s_msg(%s) {" m.tag args
    ; mkstr "  return mk_msg(MTYP_%s, %s);" m.tag pay
    ;       "}"
    ]

let c_recv_msg m =
  let pay =
    List.fold_right
      (fun t acc -> mkstr "mk_param(%s, %s)" (c_ptyp t) acc)
      m.payload
      "NULL"
  in
  String.concat "\n"
    [ mkstr "    case MTYP_%s:" m.tag
    ; mkstr "      pay = %s;" pay
    ;       "      recv_params(pay);"
    ;       "      break;"
    ]

let clib_h_subs k =
  let tm = gen_tag_map k in
  List.map (fun (f, r) -> (Str.regexp f, r))
  [ "__MSG_T_CASES__",
      fmt k.msg_decls (c_mtyp tm)
  ; "__MK_MSG_PROTOTYPES__",
      fmt k.msg_decls c_msg_ctor_proto
  ]

let clib_c_subs k =
  List.map (fun (f, r) -> (Str.regexp f, r))
  [ "__MK_MSG_FUNCS__",
      fmt k.msg_decls c_msg_ctor
  ; "__STRING_OF_MTYP_CASES__",
      fmt k.msg_decls c_mtyp_str
  ; "__RECV_MSG_CASES__",
      fmt k.msg_decls c_recv_msg
  ]
