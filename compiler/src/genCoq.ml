open Common
open Kernel

let lines l =
  l |> List.filter ((<>) "")
    |> String.concat "\n"

let fmt l f =
  l |> List.map f
    |> lines

let fmti l f =
  l |> mapi f
    |> lines

let coq_of_typ = function
  | Num -> "num"
  | Str -> "str"
  | Fdesc -> "fdesc"
  | Chan -> "tchan"

let coq_recv_typ = function
  | Num -> "recv_num", "RecvNum"
  | Str -> "recv_str", "RecvStr"
  | Fdesc -> "recv_fd", "RecvFD_t"
  | Chan -> "recv_fd", "RecvChan_t"

let coq_send_typ = function
  | Num -> "send_num", "SendNum"
  | Str -> "send_str", "SendStr"
  | Fdesc -> "send_fd", "SendFD_t"
  | Chan -> "send_fd", "SendChan_t"

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

(* symbolic state
 *
 * Track current value of state var during a handler's symbolic execution.
 * For example, after [a := a + 1], [a] is mapped to [a + 1].
 *)

type sstate = (id * expr) list

let lkup_var st id =
  try
    List.assoc id st
  with Not_found ->
    Var id

let rec lkup_expr st = function
  | Var id      -> lkup_var st id
  | NumLit i    -> NumLit i
  | StrLit s    -> StrLit s
  | Plus (a, b) -> Plus (lkup_expr st a, lkup_expr st b)

let lkup_msg_expr st m =
  { m with payload = List.map (lkup_expr st) m.payload }

let lkup_st_fields sstate kernel =
  kernel.var_decls
    |> List.map (fun v -> lkup_var sstate (fst v))
    |> List.map (fun e -> mkstr "(%s)" (coq_of_expr e))
    |> lines

let set_var st id expr =
  (id, lkup_expr st expr) :: st

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
  if m.payload = [] then
    "(" ^ m.tag ^ ")"
  else
    m.payload
      |> List.map coq_of_expr
      |> String.concat ") ("
      |> mkstr "(%s (%s))" m.tag

let coq_of_frame fr =
  fr |> List.map (mkstr "%s * ")
     |> String.concat ""
     |> mkstr "%semp"

type prog_acc =
  { code   : string
  ; frame  : string list
  ; comps  : string list
  ; sstate : sstate
  ; trace_impl : string
  ; trace_spec : string
  }

let fresh_chan_id () =
  mkstr "c%d" (tock ())

let extract_bound c fr =
  let s = mkstr "bound %s" c in
  let rec aux = function
  | [] -> raise Not_found
  | h :: t ->
    if h = s
    then t
    else if h = "all_bound comps"
    then mkstr "all_bound_drop comps %s" c :: t
    else h :: aux t
  in aux fr

let coq_of_cmd k pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^
          (let fr' = extract_bound c pacc.frame in
          mkstr "
send_msg %s %s
(tr ~~~ %s)
<@> %s;;
"
            c (coq_of_msg_expr m)
            pacc.trace_impl (coq_of_frame fr'))
      ; trace_impl =
          mkstr "SendMsg %s %s ++ %s"
            c (coq_of_msg_expr m) pacc.trace_impl
      ; trace_spec =
          mkstr "SendMsg %s %s ++ %s"
            c (coq_of_msg_expr (lkup_msg_expr pacc.sstate m)) pacc.trace_spec

      }
  | Call (res, f, arg) ->
      { pacc with code = pacc.code ^
          mkstr "
%s <- call %s %s
(tr ~~~ %s)
<@> %s;"
            res (coq_of_expr f) (coq_of_expr arg)
            pacc.trace_impl (coq_of_frame pacc.frame)
      ; trace_impl =
          mkstr "Call_t %s %s %s ++ %s"
            (coq_of_expr f)
            (coq_of_expr arg)
            res pacc.trace_impl
      ; trace_spec =
          mkstr "Call_t %s %s %s ++ %s"
            (coq_of_expr (lkup_expr pacc.sstate f))
            (coq_of_expr (lkup_expr pacc.sstate arg))
            res pacc.trace_spec
      }
  | Spawn (res, comp) ->
      let path = List.assoc comp k.components in
      { pacc with code = pacc.code ^
          mkstr "
%s <- exec %s (string2str \"%s\")
(tr ~~~ %s)
<@> %s;
"
            res comp path
            pacc.trace_impl (coq_of_frame pacc.frame)
      ; trace_impl =
          mkstr "Exec_t (string2str \"%s\") %s ++ %s"
            path res pacc.trace_impl
      ; trace_spec =
          mkstr "Exec_t (string2str \"%s\") %s ++ %s"
            path res pacc.trace_spec
      ; frame =
          mkstr "bound %s" res :: pacc.frame
      ; comps =
          res :: pacc.comps
      }
  | Assign (id, expr) ->
      { pacc with code = pacc.code ^
          (* TODO should this expr be expanded first ? *)
          mkstr "\nlet %s := %s in" id (coq_of_expr expr)
      ; sstate =
          set_var pacc.sstate id expr
      }

let coq_of_prog s tr0 fr0 p =
  let rec loop pacc = function
    | Nop ->
        { pacc with code = pacc.code ^ "\n(* Nop *)\n" }
    | Seq (c, p') ->
        loop (coq_of_cmd s pacc c) p'
  in
  let pacc0 =
    { code   = ""
    ; frame  = fr0
    ; comps  = []
    ; sstate = []
    ; trace_impl = tr0
    ; trace_spec = tr0
    }
  in
  loop pacc0 p

let coq_trace_spec_of_prog s fr p =
  (coq_of_prog s "" fr p).trace_spec

let coq_trace_impl_of_prog s fr p =
  (coq_of_prog s "" fr p).trace_impl

let sstate_of_prog s fr p =
  (coq_of_prog s "" fr p).sstate

let rec expr_vars = function
  | Var id -> [id]
  | Plus (e1, e2) -> expr_vars e1 @ expr_vars e2
  | _ -> []

(* vars that need forall binding *)
let cmd_vars = function
  | Send (c, m) ->
      c :: List.flatten (List.map expr_vars m.payload)
  | Call (var, func, arg) ->
      var :: expr_vars arg
  | Spawn (res, path) ->
      [res]
  | Assign (id, expr) ->
      [] (* get bound in a let *)

let rec prog_vars = function
  | Nop -> []
  | Seq (c, p) -> cmd_vars c @ prog_vars p

let coq_of_msg_pat m =
  mkstr "| %s %s =>" m.tag
    (String.concat " " m.payload)

let handler_vars xch_chan trig prog =
    uniq (xch_chan :: trig.payload @ prog_vars prog)

(* handler vars modulo global state vars *)
let handler_vars_nonstate xch_chan trig prog svars =
  let globals =
    List.map (fun (id, typ) -> id) svars
  in
  List.filter
    (fun x -> not (List.mem x globals))
    (handler_vars xch_chan trig prog)

let coq_of_cond_prop = function
  | Always        -> "True"
  | NumEq (id, i) -> mkstr "(nat_of_num %s = %d)" id i

let coq_of_cond_spec prev_conds cond =
  let context =
    prev_conds
      |> List.map (fun c -> mkstr "~ %s -> " (coq_of_cond_prop c))
      |> String.concat ""
  in
  mkstr "%s%s ->" context (coq_of_cond_prop cond)

(* TODO what about chans produced by Spawn ? *)
let chans_of_cmd = function
  | Send (c, _) -> [c]
  | _ -> []

let rec chans_of_prog = function
  | Nop -> []
  | Seq (c, p) -> chans_of_cmd c @ chans_of_prog p

let coq_spec_of_handler s comp xch_chan trig conds index tprog =
  let fr0 =
    List.map
      (fun c -> mkstr "bound %s" c)
      (xch_chan :: chans_of_prog tprog.program)
  in
  let pacc = coq_of_prog s "" fr0 tprog.program in
  let hdr =
    mkstr "
| VE_%s_%s_%d : \nforall %s, %s\nValidExchange (mkst (%scomps)"
      comp trig.tag index
      (String.concat " " ((handler_vars_nonstate xch_chan trig tprog.program s.var_decls)))
      (coq_of_cond_spec conds tprog.condition)
      (String.concat "" (List.map (fun c -> mkstr "%s :: " c) pacc.comps))
  in
  let ftr =
    mkstr "(tr ~~~ ((%s RecvMsg %s (%s %s)) ++ tr))"
      pacc.trace_spec
      xch_chan
      trig.tag
      (String.concat " " trig.payload)
  in
  lines [hdr; ftr; lkup_st_fields pacc.sstate s; ")"]

let coq_of_init k =
  let pacc = coq_of_prog k "tr" [] k.init in
  lines
    [ "let tr := inhabits nil in"
    ; pacc.code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        (String.concat "" (List.map (mkstr "%s :: ") pacc.comps))
        pacc.trace_impl
        (lkup_st_fields pacc.sstate k)
    ]

let coq_of_cond index = function
  | Always ->
      if index = 0 then "" else " else "
  | NumEq (id, v) ->
      lines
        [ if index > 0 then " else " else ""
        ; mkstr "if (Peano_dec.eq_nat_dec (nat_of_num %s) %d) then " id v
        ]

let st_fields_in_comps k =
  k.var_decls
    |> List.filter (fun (_, typ) -> typ = Chan)
    |> List.map (fun (id, _) -> mkstr "[In %s comps]" id)

let coq_of_handler k xch_chan trig index tprog =
  let tr =
    mkstr "RecvMsg %s (%s %s) ++ tr"
      xch_chan trig.tag (String.concat " " trig.payload)
  in
  let fr =
    st_fields_in_comps k @
      [ "all_bound comps"
      ; mkstr "[In %s comps]" xch_chan
      ; "(tr ~~ [KInvariant kst])"
      ]
  in
  let pacc = coq_of_prog k tr fr tprog.program in
  lines
    [ coq_of_cond index tprog.condition ^ " ("
    ; pacc.code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s) %s) }}"
        (String.concat "" (List.map (mkstr "%s :: ") pacc.comps))
        pacc.trace_impl
        (String.concat " " (List.map fst k.var_decls))
     ;" ) "
    ]

let msg_pat_of_msg_decl m =
  { tag = m.tag
  ; payload = List.map (fun _ -> mkstr "__dummy_%d__" (tock ())) m.payload
  }

let coq_of_exchange spec xch_chan comp =
  let var_ext =
    fmt spec.var_decls (fun (id, _) ->
      mkstr "pose (%s := (%s kst));" id id)
  in
  let fields_in_comps =
    st_fields_in_comps spec
      |> List.map (mkstr "%s * ")
      |> String.concat ""
      |> mkstr "%semp"
  in
  let comp_handlers =
    try List.assoc comp (snd spec.exchange)
    with Not_found -> []
  in
  let dummy_handler t =
    { trigger = t
    ; responds = [{condition = Always; program = Nop}]
    }
  in
  let get_handler msg =
    try List.find (fun h -> h.trigger.tag = msg.tag) comp_handlers
    with Not_found -> dummy_handler (msg_pat_of_msg_decl msg)
  in
  let hands =
    fmt spec.msg_decls (fun msg ->
      let h = get_handler msg in
      lines
        [ coq_of_msg_pat h.trigger
        ; fmti h.responds (coq_of_handler spec xch_chan h.trigger)
        ]
    )
  in
  let kstate_vars =
    String.concat " " (List.map fst spec.var_decls)
  in
  mkstr "
Definition exchange_%s :
  forall (c : tchan) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros c kst;
  pose (comps := (components kst));
  pose (tr := (ktr kst));
%s
  refine (
    req <- recv_msg c tr
    <@> [In c comps] * %s * all_bound_drop comps c * (tr ~~ [KInvariant kst]);
    match req with
%s
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c (BadTag tag) ++ tr) %s) }}
    end
  );  sep unfoldr simplr.
Qed.
"
  comp var_ext fields_in_comps hands kstate_vars


let coq_of_kernel_subs s =
  let m = gen_tag_map s in
  let (xch_chan, exchanges) = s.exchange in
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "CONST_DECLS",
      fmt s.constants coq_of_constant_decl
  ; "COMP_DECLS",
      fmt s.components (fun (id, path) ->
        "| " ^ id)
  ; "CHAN_PATHS",
      fmt s.components (fun (id, path) ->
        mkstr "  | %s => string2str \"%s\"" id path)
  ; "MSG_DECL",
      fmt s.msg_decls coq_of_msg_decl
  ; "RECV_T_CASES",
      fmt s.msg_decls (coq_trace_recv_msg m)
  ; "SEND_T_CASES",
      fmt s.msg_decls (coq_trace_send_msg m)
  ; "RECV_CASES",
      fmt s.msg_decls (coq_recv_msg m)
  ; "SEND_CASES",
      fmt s.msg_decls (coq_send_msg m)
  ; "KTRACE_VAR_DECLS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "let %s := (%s s) in\n" id id)))
  ; "KTRACE_VAR_LISTS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ; "VE_STATE_VAR_DECLS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "Let %s := (%s s).\n" id id)))
  ; "VE_STATE_VAR_LISTS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ; "VE_HANDLED_CASES",
      fmt exchanges (fun (comp, handlers) ->
      fmt handlers
        (fun h ->
          String.concat "\n" (snd (
          List.fold_left
            (fun ((idx, conds), res) tprog ->
            ((idx + 1, tprog.condition :: conds),
             (coq_spec_of_handler s comp xch_chan h.trigger conds idx tprog) :: res))
            ((0, []), [])
            h.responds))
        )
      )
  ; "VE_UNHANDLED_CASES",
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
  forall %s %s, ValidExchange (mkst comps (tr ~~~ (RecvMsg %s (%s %s) ++ tr)) %s ) "
            comp m.tag args xch_chan xch_chan m.tag args ((fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id))))
        )
      )
  ; "KTRACE_INIT", (
      let pacc = coq_of_prog s "" [] s.init in
      mkstr "forall %s,\nKInvariant (mkst (%snil) [%snil] %s)"
        (String.concat " " (prog_vars s.init))
        (String.concat "" (List.map (fun c -> mkstr "%s :: " c) pacc.comps))
        pacc.trace_impl (* TODO should this use trace_spec ? *)
        (lkup_st_fields pacc.sstate s)
    )
  ; "STATE_FIELDS", (
      let declstr = (String.concat ";" (List.map (fun (id, typ) ->
        mkstr " %s : %s " id (coq_of_typ typ)) s.var_decls)) in
      (match (s.var_decls) with
      | [] -> declstr
      | _ -> mkstr ("; %s") declstr)
  )
  ; "KSTATE_INVS",
      fmt s.var_decls (fun (id, typ) ->
        match typ with
        | Chan -> mkstr "* [In (%s s) (components s)]" id
        | _    -> ""
      )
  ; "INIT_CODE",
      coq_of_init s
  ; "EXCHANGES",
      fmt s.components (fun (comp, _) ->
        coq_of_exchange s xch_chan comp)
      (* fmt exchanges (coq_of_exchange s xch_chan) *)
  ; "TYPE_OF_COMP_DEFAULT",
      mkstr "\n| nil => %s (* TODO: need default or proof *)"
        (fst (List.hd s.components))
  ; "KBODY",
      let comp_xch =
        s.components
          |> List.map (fun (c, _) -> mkstr "\n| %s => exchange_%s" c c)
          |> String.concat ""
      in
      let fields_in_comps =
        st_fields_in_comps s
          |> List.map (mkstr "%s * ")
          |> String.concat ""
          |> mkstr "%semp"
      in
      mkstr "
  intros kst.
  pose (comps := (components kst));
  pose (tr := (ktr kst));
  %s
  refine (
    comp <- select comps tr
    <@> (tr ~~ [KInvariant kst] * all_bound comps * %s);
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
      (fmt s.var_decls (fun (id,typ) -> (mkstr "pose (%s := (%s kst));" id id)))
      fields_in_comps
      comp_xch
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ]
