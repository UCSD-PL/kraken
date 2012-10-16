open Common
open Kernel

let lines l =
  l |> List.filter ((<>) "")
    |> String.concat "\n"

let fmt l f =
  l |> List.map f
    |> lines

let mk_buffer () =
  let b = Buffer.create 16 in
  (Buffer.add_string b, fun () -> Buffer.contents b)

let coq_of_typ = function
  | Num -> "num"
  | Str -> "str"
  | Fdesc -> "fdesc"

let coq_recv_typ = function
  | Num -> "recv_num", "RecvNum"
  | Str -> "recv_str", "RecvStr"
  | Fdesc -> "recv_fd", "RecvFD_t"

let coq_send_typ = function
  | Num -> "send_num", "SendNum"
  | Str -> "send_str", "SendStr"
  | Fdesc -> "send_fd", "SendFD_t"

let coq_of_num i =
  mkstr "(Num \"%03d\")" i

let coq_of_string s =
  s |> explode
    |> List.map (mkstr "\"%c\" :: ")
    |> String.concat ""
    |> mkstr "(%snil)"

let rec coq_of_expr = function
  | Var id -> id
  | NumLit i -> coq_of_num i
  | StrLit s -> coq_of_string s
  | Plus(a, b) ->
    mkstr "(num_of_nat ((nat_of_num (%s)) + (nat_of_num (%s))))"
      (coq_of_expr a) (coq_of_expr b)

let coq_of_constant_decl (id, e) =
  mkstr "
Definition %s := %s.
" id (coq_of_expr e)

let coq_of_msg_decl m =
  mkstr "| %s : %s" m.tag
    (m.payload
      |> List.map coq_of_typ
      |> List.map (mkstr "%s -> ")
      |> String.concat ""
      |> mkstr "%smsg")

let str_of_args m =
  m.payload
    |> mapi (fun i _ -> mkstr "p%d" i)
    |> String.concat " "

let coq_trace_recv_msg tag_map m =
  let hdr =
    mkstr "| %s %s =>" m.tag (str_of_args m)
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
        |> lines
  in
  let tag =
    mkstr "RecvNum c (Num \"%03d\")"
      (List.assoc m.tag tag_map)
  in
  lines [hdr; pay; tag]

(* WARNING copy/paste of coq_trace_recv_msg *)
let coq_trace_send_msg tag_map m =
  let hdr =
    mkstr "| %s %s =>" m.tag (str_of_args m)
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
        |> lines
  in
  let tag =
    mkstr "SendNum c (Num \"%03d\")"
      (List.assoc m.tag tag_map)
  in
  lines [hdr; pay; tag]

(* recv msg on bound chan "c" *)
let coq_recv_msg tag_map m =
  let hdr =
    mkstr "| Num \"%03d\" => (* %s *)"
      (List.assoc m.tag tag_map) m.tag
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
      mkstr "RecvNum c (Num \"%03d\") ++ tr"
        (List.assoc m.tag tag_map)
    in
    m.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
      |> List.rev
      |> lines
  in
  let ret =
    mkstr "{{ Return (%s %s) }}\n" m.tag (str_of_args m)
  in
  lines [hdr; pay; ret]

(* send msg on bound chan "c" *)
(* WARNING copy/paste of coq_recv_msg *)
let coq_send_msg tag_map m =
  let hdr = lines
    [ mkstr "| %s %s =>" m.tag (str_of_args m)
    ; mkstr "send_num c (Num \"%03d\") tr;;" (List.assoc m.tag tag_map)
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
      mkstr "SendNum c (Num \"%03d\") ++ tr"
        (List.assoc m.tag tag_map)
    in
    m.payload
      |> List.fold_left aux (0, [], tr)
      |> fun (_, x, _) -> x
      |> List.rev
      |> lines
  in
  let ret =
    "{{ Return tt }}"
  in
  lines [hdr; pay; ret]

let coq_of_msg_expr m =
  mkstr "(%s %s)" m.tag
    (m.payload
      |> List.map coq_of_expr
      |> String.concat ") ("
      |> mkstr "(%s)")

let coq_of_frame fr =
  fr |> List.map (mkstr "%s * ")
     |> String.concat ""
     |> mkstr "%semp"

type prog_acc =
  { code  : string
  ; trace : string
  ; frame : string list
  ; comps : string list
  }

let fresh_chan_id () =
  mkstr "c%d" (tock ())

let coq_of_cmd s pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^
          (let fr' = remove (mkstr "bound %s" c) pacc.frame in
          mkstr "
send_msg %s %s
(tr ~~~ %s)
<@> %s;;
"
            c (coq_of_msg_expr m)
            pacc.trace (coq_of_frame fr'))
      ; trace =
          mkstr "SendMsg %s %s ++ %s"
            c (coq_of_msg_expr m) pacc.trace
      }
  | Call (res, f, arg) ->
      { pacc with code = pacc.code ^
          mkstr "
%s <- call %s %s
(tr ~~~ %s)
<@> %s;"
            res (coq_of_expr f) (coq_of_expr arg)
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "Call_t %s %s %s ++ %s"
            (coq_of_expr f) (coq_of_expr arg) res pacc.trace
      }
  | Spawn (res, comp) ->
      let path =
        snd (List.find (fun (id, _) -> id = comp) s.components)
      in
      { code = pacc.code ^
          mkstr "
%s <- exec %s (string2str \"%s\")
(tr ~~~ %s)
<@> %s;
"
            res comp path
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "Exec_t (string2str \"%s\") %s ++ %s"
            path res pacc.trace
      ; frame =
          mkstr "bound %s" res :: pacc.frame
      ; comps =
          res :: pacc.comps
      }
  | Assign (id, expr) ->
      { pacc with
        code = (
          let (add, contents) = mk_buffer () in
          add pacc.code;
          add (mkstr "
let %s := %s in" id (coq_of_expr expr));
          contents ()
        )
      }

let coq_of_prog s tr0 fr0 p =
  let rec loop pacc = function
    | Nop -> pacc
    | Seq (c, p') -> loop (coq_of_cmd s pacc c) p'
  in
  loop {code = ""; trace = tr0; frame = fr0; comps = []} p

let coq_trace_of_prog s fr p =
  (coq_of_prog s "" fr p).trace

let expr_vars = function
  | Var id -> [id]
  | _ -> []

let cmd_vars = function
  | Send (c, m) ->
      c :: List.flatten (List.map expr_vars m.payload)
  | Call (var, func, arg) ->
      var :: expr_vars arg
  | Spawn (res, path) ->
      [res]
  | Assign (id, expr) ->
      []

let rec prog_vars = function
  | Nop -> []
  | Seq (c, p) -> cmd_vars c @ prog_vars p

let coq_of_msg_pat m =
  mkstr "| %s %s =>" m.tag
    (String.concat " " m.payload)

let handler_vars xch_chan h =
  uniq (xch_chan :: h.trigger.payload @ prog_vars h.respond)

let coq_spec_of_handler s comp xch_chan h =
  let hdr =
    mkstr "
| VE_%s_%s :\nforall %s,\nValidExchange ("
      comp
      h.trigger.tag
      (String.concat " " (handler_vars xch_chan h))
  in
  let bdy =
    if h.respond = Nop then
      "      (* no response *)"
    else
      let fr = [ mkstr "bound %s" xch_chan ] in
      coq_trace_of_prog s fr h.respond
  in
  let ftr =
    mkstr "RecvMsg %s (%s %s))"
      xch_chan
      h.trigger.tag
      (String.concat " " h.trigger.payload)
  in
  lines [hdr; bdy; ftr]

let coq_of_init s =
  let cp = coq_of_prog s "tr" [] s.init in
  lines
    [ "let tr := inhabits nil in"
    ; if cp.code = ""
      then "        (* no code *)"
      else cp.code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        (cp.comps |> List.map (mkstr "%s :: ") |> String.concat "")
        cp.trace
        (s.var_decls |> List.map fst |> String.concat " ")
    ]

let coq_of_handler s xch_chan h =
  let tr =
    mkstr "RecvMsg %s (%s %s) ++ tr"
      xch_chan
      h.trigger.tag
      (String.concat " " h.trigger.payload)
  in
  let fr =
    [ mkstr "[In %s comps]" xch_chan
    ; mkstr "bound %s" xch_chan
    ; mkstr "all_bound_drop comps %s" xch_chan
    ; "(tr ~~ [KTrace tr])"
    ]
  in
  let pacc = coq_of_prog s tr fr h.respond in
  lines
    [ coq_of_msg_pat h.trigger
    ; if pacc.code = "" then
        "        (* no code *)"
      else
        pacc.code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s) %s) }}"
        (pacc.comps |> List.map (mkstr "%s :: ") |> String.concat "")
        pacc.trace
        (s.var_decls |> List.map fst |> String.concat " ")
    ]

let coq_of_exchange spec xch_chan kstate_vars (comp, handlers) =
  let hands =
    fmt handlers (coq_of_handler spec xch_chan)
  in
  let handled m =
    List.exists (fun h -> h.trigger.tag = m.tag) handlers
  in
  let unhandled_msgs =
    List.filter (fun m -> not (handled m)) spec.msg_decls
  in
  let fall_through =
    match unhandled_msgs with
    | [] -> ""
    | _ -> mkstr "
    (* unhandled cases *)
    | msg =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c msg ++ tr) %s) }}
"
      kstate_vars
  in
  (* TODO c should be %s xch_chan, but there's plenty of them :( *)
  mkstr "
Definition exchange_%s :
  forall (c : tchan) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros c [comps tr %s]; refine (
    req <- recv_msg c tr
    <@> [In c comps] * all_bound_drop comps c * (tr ~~ [KTrace tr]);
    match req with
%s
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c (BadTag tag) ++ tr) %s) }}
%s    end
  );
  sep unfoldr simplr.
Qed.
"
  comp kstate_vars hands kstate_vars fall_through

let coq_of_kernel_subs s =
  let m = gen_tag_map s in
  let (xch_chan, exchanges) = s.exchange in
  let kstate_vars =
    s.var_decls |> List.map fst |> String.concat " "
  in
  List.map (fun (f, r) -> (Str.regexp f, r))
  [ "__P_CONST_DECLS__",
      fmt s.constants coq_of_constant_decl
  ; "__P_COMP_DECLS__",
      fmt s.components (fun (id, path) ->
        "| " ^ id)
  ; "__P_CHAN_PATHS__",
      fmt s.components (fun (id, path) ->
        mkstr "  | %s => string2str \"%s\"" id path)
  ; "__P_MSG_DECL__",
      fmt s.msg_decls coq_of_msg_decl
  ; "__P_RECV_T_CASES__",
      fmt s.msg_decls (coq_trace_recv_msg m)
  ; "__P_SEND_T_CASES__",
      fmt s.msg_decls (coq_trace_send_msg m)
  ; "__P_RECV_CASES__",
      fmt s.msg_decls (coq_recv_msg m)
  ; "__P_SEND_CASES__",
      fmt s.msg_decls (coq_send_msg m)
  ; "__P_VE_HANDLED_CASES__",
      fmt exchanges (fun (comp, handlers) ->
        fmt handlers (coq_spec_of_handler s comp xch_chan))
  ; "__P_VE_UNHANDLED_CASES__",
      fmt exchanges (fun (comp, handlers) ->
        let handled m =
          List.exists (fun h -> h.trigger.tag = m.tag) handlers
        in
        let unhandled_msgs =
          List.filter (fun m -> not (handled m)) s.msg_decls
        in
        fmt unhandled_msgs (fun m ->
          let args = m.payload |> List.map coq_of_typ |> String.concat " " in
          mkstr "
| VE_%s_%s:
  forall %s %s, ValidExchange (RecvMsg %s (%s %s))"
            comp m.tag args xch_chan xch_chan m.tag args
        )
      )
  ; "__P_KTRACE_INIT__", (
      let t = coq_trace_of_prog s [] s.init in
      let v = prog_vars s.init in
      match v with
      | [] -> mkstr "KTrace (%snil)" t
      | _  -> mkstr "forall %s, KTrace (%snil)" (String.concat " " v) t
    )
  ; "__P_KSTATE_FIELDS__",
      fmt s.var_decls (fun (id, typ) ->
        mkstr "; %s : %s" id (coq_of_typ typ))
  ; "__P_INIT_CODE__",
      coq_of_init s
  ; "__P_EXCHANGES__",
      fmt exchanges (coq_of_exchange s xch_chan kstate_vars)
  ; "__P_TYPE_OF_COMP_DEFAULT__",
      mkstr "\n| nil => %s (* TODO: need default or proof *)"
        (fst (List.hd s.components))
  ; "__P_KBODY__",
      let comp_xch =
        s.components
          |> List.map (fun (c, _) -> mkstr "\n| %s => exchange_%s" c c)
          |> String.concat ""
      in
      mkstr "
  intros [comps tr %s];
  refine (
    comp <- select comps tr
    <@> (tr ~~ [KTrace tr] * all_bound comps);
    let handler := (
      match type_of_comp comp comps with
%s
      end
    ) in
    s' <- handler comp (mkst comps (tr ~~~ Select comps comp :: tr) %s);
    {{ Return s' }}
  );
  sep unfoldr simplr.
"
      kstate_vars comp_xch kstate_vars
  ]
