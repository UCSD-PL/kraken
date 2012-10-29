open Common
open Kernel
open Gen

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
  { code  : string
  ; trace : string
  ; frame : string list
  ; comps : string list
  }

let fresh_chan_id () =
  mkstr "c%d" (tock ())

let extract_bound c fr =
  let s = mkstr "bound %s" c in
  let rec aux = function
    | [] -> raise Not_found
    | h :: t ->
      if h = s then
        t
      else if h = "all_bound comps" then
        mkstr "all_bound_drop comps %s" c :: t
      else
        h :: aux t
  in
  aux fr

let coq_of_cmd s pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^
          (let fr' = extract_bound c pacc.frame in
          mkstr "
send_msg %s %s
(tr ~~~ expand_ktrace (%s))
<@> %s;;
"
            c (coq_of_msg_expr m)
            pacc.trace (coq_of_frame fr'))
      ; trace =
          mkstr "KSend %s %s :: %s"
            c (coq_of_msg_expr m) pacc.trace
      }
  | Call (res, f, arg) ->
      { pacc with code = pacc.code ^
          mkstr "
%s <- call %s %s
(tr ~~~ expand_ktrace (%s))
<@> %s;"
            res (coq_of_expr f) (coq_of_expr arg)
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "KCall %s %s %s :: %s"
            (coq_of_expr f) (coq_of_expr arg) res pacc.trace
      }
  | Spawn (res, comp) ->
      let path =
        snd (List.find (fun (id, _) -> id = comp) s.components)
      in
      { code = pacc.code ^
          mkstr "
%s <- exec %s (str_of_string \"%s\")
(tr ~~~ expand_ktrace (%s))
<@> %s;
"
            res comp path
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "KExec (str_of_string \"%s\") %s :: %s"
            path res pacc.trace
      ; frame =
          mkstr "bound %s" res :: pacc.frame
      ; comps =
          res :: pacc.comps
      }
  | Assign (id, expr) ->
      { pacc with
         code = pacc.code ^
           mkstr "\nlet %s := %s in" id (coq_of_expr expr)
      }

let coq_of_prog s tr0 fr0 p =
  let rec loop pacc = function
    | Nop -> pacc
    | Seq (c, p') -> loop (coq_of_cmd s pacc c) p'
  in
  loop {code = ""; trace = tr0; frame = fr0; comps = []} p

let coq_trace_of_prog s fr p =
  (coq_of_prog s "" fr p).trace

let rec expr_vars = function
  | Var id -> [id]
  | Plus (e1, e2) -> expr_vars e1 @ expr_vars e2
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

module OrderedChan =
  struct
    type t = chan
    let compare = compare
  end

module ChanSet = Set.Make(OrderedChan);;

let chans_of_cmd = function
| Send(c, _)    -> ChanSet.singleton c
| Call(_, _, _) -> ChanSet.empty
| Spawn(_, _)   -> ChanSet.empty
| Assign(_, _)  -> ChanSet.empty

let chans_of_prog p =
  let rec aux acc = function
    | Nop ->
        ChanSet.elements acc
    | Seq(cmd, rest) ->
        aux (ChanSet.union acc (chans_of_cmd cmd)) rest
  in
  aux ChanSet.empty p

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
      let fr = List.map
        (fun c -> mkstr "bound %s" c)
        (xch_chan :: chans_of_prog h.respond)
      in
      coq_trace_of_prog s fr h.respond
  in
  let ftr =
    mkstr "KRecv %s (%s %s) :: nil)"
      xch_chan
      h.trigger.tag
      (String.concat " " h.trigger.payload)
  in
  lcat [hdr; bdy; ftr]

let frames_of_vars k =
  k.var_decls
    |> List.filter (fun (_, typ) -> typ = Chan)
    |> List.map (fun (id, _) -> mkstr "[In %s comps]" id)

let coq_of_handler k xch_chan h =
  let tr =
    mkstr "KRecv %s (%s %s) :: tr"
      xch_chan
      h.trigger.tag
      (String.concat " " h.trigger.payload)
  in
  let fr = (
    let acc0 =
      [ "all_bound comps"
      ; mkstr "[In %s comps]" xch_chan
      ; "(tr ~~ [KTraceOK tr])"
      ]
    in
    (frames_of_vars k) @ acc0
  )
  in
  let pacc = coq_of_prog k tr fr h.respond in
  let code =
    if pacc.code = "" then
      "        (* no code *)"
    else
      pacc.code
  in
  let comps =
    pacc.comps
      |> List.map (mkstr "%s :: ")
      |> String.concat ""
  in
  let fields =
    k.var_decls
      |> List.map fst
      |> String.concat " "
  in
  lcat
    [ coq_of_msg_pat h.trigger
    ; code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s) %s) }}"
        comps pacc.trace fields
    ]

let coq_of_exchange spec xch_chan kstate_vars comp =
  let comp_handlers = (
    try Some (List.find (fun x -> fst x = comp) (snd (spec.exchange)))
    with Not_found -> None
  ) in
  let vars_frames =
    match frames_of_vars spec with
    | [] -> ""
    | l  -> " * " ^ String.concat " * " l
  in
  let hands =
    fmt spec.msg_decls (fun msg ->
      let constr = mkstr "%s %s" msg.tag (coq_of_args msg) in
      let unhandled = mkstr "
    (* not handled *)
    | %s =>
      {{ Return (mkst comps (tr ~~~ KRecv c (%s) :: tr) %s) }}
"
        constr constr kstate_vars
      in
      match comp_handlers with
      | None -> unhandled
      | Some(exchanges) ->
        try (
          let handler =
            List.find (fun h -> h.trigger.tag = msg.tag) (snd exchanges)
          in
          coq_of_handler spec xch_chan handler
        )
        with Not_found -> unhandled
    )
  in
  mkstr "
Definition exchange_%s :
  forall (c : tchan) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros c [comps tr %s]; refine (
    req <- recv_msg c (tr ~~~ expand_ktrace tr)
    <@> [In c comps]%s * all_bound_drop comps c * (tr ~~ [KTraceOK tr]);
    match req with
%s
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ KRecv c (BadTag tag) :: tr) %s) }}
    end
  );
  sep unfoldr simplr.
Qed.
"
  comp kstate_vars vars_frames hands kstate_vars

let coq_of_init k =
  let cp = coq_of_prog k "tr" [] k.init in
  let code =
    if cp.code = "" then
      "        (* no code *)"
    else
      cp.code
  in
  let comps =
    cp.comps
      |> List.map (mkstr "%s :: ")
      |> String.concat ""
  in
  let fields =
    k.var_decls
      |> List.map fst
      |> String.concat " "
  in
  lcat
    [ "let tr := inhabits nil in"
    ; code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        comps cp.trace fields
    ]

let coq_of_prop (name, prop) : string =
  match prop with
  | ImmAfter (bef, aft) ->
      mkstr "
Theorem %s :
  forall chan msg,
  valid_msg msg ->
  ImmAfter
    (%s)
    (%s).
Proof.
  unfold ImmAfter; induction 2; intros; imm_tac.
Qed.
" name bef aft
  | ImmBefore (bef, aft) ->
      mkstr "
Theorem %s :
  forall chan msg,
  valid_msg msg ->
  ImmBefore
    (%s)
    (%s).
Proof.
  unfold ImmBefore; induction 2; intros; imm_tac.
Qed.
" name bef aft

let subs s =
  let (xch_chan, exchanges) = s.exchange in
  let kstate_vars =
    s.var_decls |> List.map fst |> String.concat " "
  in
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "VE_HANDLED_CASES",
      fmt exchanges (fun (comp, handlers) ->
        fmt handlers (coq_spec_of_handler s comp xch_chan))
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
  forall %s %s, ValidExchange (KRecv %s (%s %s) :: nil)"
            comp m.tag args xch_chan xch_chan m.tag args
        )
      )
  ; "KTRACE_INIT", (
      let t = coq_trace_of_prog s [] s.init in
      let v = prog_vars s.init in
      match v with
      | [] -> mkstr "KTraceOK (%snil)" t
      | _  -> mkstr "forall %s, KTraceOK (%snil)" (String.concat " " v) t
    )
  ; "KSTATE_FIELDS",
      fmt s.var_decls (fun (id, typ) ->
        mkstr "; %s : %s" id (coq_of_typ typ))
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
        coq_of_exchange s xch_chan kstate_vars comp)
  ; "TYPE_OF_COMP_DEFAULT",
      mkstr "\n| nil => %s (* TODO: need default or proof *)"
        (fst (List.hd s.components))
  ; "KBODY", (
      let comp_xch =
        s.components
          |> List.map (fun (c, _) -> mkstr "\n| %s => exchange_%s" c c)
          |> String.concat ""
      in
      let kstate_invs =
        match frames_of_vars s with
        | [] -> ""
        | l  -> " * " ^ String.concat " * " l
      in
      mkstr "
  intros [comps tr %s];
  refine (
    comp <- select comps (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [KTraceOK tr] * all_bound comps%s);
    let handler := (
      match type_of_comp comp comps with
%s
      end
    ) in
    s' <- handler comp (mkst comps (tr ~~~ KSelect comps comp :: tr) %s);
    {{ Return s' }}
  );
  sep unfoldr simplr.
"
      kstate_vars kstate_invs comp_xch kstate_vars)
  ; "PROPERTIES",
      fmt s.props coq_of_prop
  ]
