open Common
open Kernel
open Gen

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
    |> lcat

let set_var st id expr =
  (id, lkup_expr st expr) :: st

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


type prog_acc =
  { code   : string
  ; frame  : string list
  ; comps  : string list
  ; sstate : sstate
  ; trace_impl : string
  ; trace_spec : string
  }

let coq_of_cmd k pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^
          (let fr' = extract_bound c pacc.frame in
          mkstr "
send_msg %s %s
(tr ~~~ expand_ktrace (%s))
<@> %s;;
"
            c (coq_of_msg_expr m)
            pacc.trace_impl (coq_of_frame fr'))
      ; trace_impl =
          mkstr "KSend %s %s :: %s"
            c (coq_of_msg_expr m) pacc.trace_impl
      ; trace_spec =
          mkstr "KSend %s %s :: %s"
            c (coq_of_msg_expr (lkup_msg_expr pacc.sstate m)) pacc.trace_spec

      }
  | Call (res, f, arg) ->
      { pacc with code = pacc.code ^
          mkstr "
%s <- call %s %s
(tr ~~~ expand_ktrace (%s))
<@> %s;"
            res (coq_of_expr f) (coq_of_expr arg)
            pacc.trace_impl (coq_of_frame pacc.frame)
      ; trace_impl =
          mkstr "KCall %s %s %s :: %s"
            (coq_of_expr f)
            (coq_of_expr arg)
            res pacc.trace_impl
      ; trace_spec =
          mkstr "KCall %s %s %s :: %s"
            (coq_of_expr (lkup_expr pacc.sstate f))
            (coq_of_expr (lkup_expr pacc.sstate arg))
            res pacc.trace_spec
      }
  | Spawn (res, comp) ->
      let path = List.assoc comp k.components in
      { pacc with code = pacc.code ^
          mkstr "
%s <- exec %s (str_of_string \"%s\")
(tr ~~~ expand_ktrace (%s))
<@> %s;
"
            res comp path
            pacc.trace_impl (coq_of_frame pacc.frame)
      ; trace_impl =
          mkstr "KExec (str_of_string \"%s\") %s :: %s"
            path res pacc.trace_impl
      ; trace_spec =
          mkstr "KExec (str_of_string \"%s\") %s :: %s"
            path res pacc.trace_spec
      ; frame =
          mkstr "bound %s" res :: pacc.frame
      ; comps =
          res :: pacc.comps
      }
  | Assign (id, expr) ->
      { pacc with code = pacc.code ^
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
      []

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

let coq_spec_of_handler k comp xch_chan trig conds index tprog =
  let fr0 =
    List.map
      (fun c -> mkstr "bound %s" c)
      (xch_chan :: chans_of_prog tprog.program)
  in
  let pacc = coq_of_prog k "" fr0 tprog.program in
  lcat
    [ mkstr "| VE_%s_%s_%d :"
        comp trig.tag index
    ; mkstr "forall %s,"
        (String.concat " " (handler_vars_nonstate xch_chan trig tprog.program k.var_decls))
    ; coq_of_cond_spec conds tprog.condition
    ; "ValidExchange (mkst"
    ; mkstr "  (%scomps)"
        (String.concat "" (List.map (fun c -> mkstr "%s :: " c) pacc.comps))
    ; mkstr "  (tr ~~~ %sKRecv %s (%s %s) :: tr)"
        pacc.trace_spec xch_chan trig.tag
        (String.concat " " trig.payload)
    ; mkstr "  %s"
        (lkup_st_fields pacc.sstate k)
    ; ")"
    ]

let coq_of_cond index = function
  | Always ->
      if index = 0 then "" else " else "
  | NumEq (id, v) ->
      lcat
        [ if index > 0 then " else " else ""
        ; mkstr "if (Peano_dec.eq_nat_dec (nat_of_num %s) %d) then " id v
        ]

let fields_in_comps k =
  k.var_decls
    |> List.filter (fun (_, typ) -> typ = Chan)
    |> List.map (fun (id, _) -> mkstr "[In %s comps]" id)

let fields_in_comps_fr k =
  fields_in_comps k
    |> List.map (mkstr "%s * ")
    |> String.concat ""
    |> mkstr "%semp"

let coq_of_handler k xch_chan trig index tprog =
  let tr =
    mkstr "KRecv %s (%s %s) :: tr"
      xch_chan trig.tag (String.concat " " trig.payload)
  in
  let fr =
    fields_in_comps k @
      [ "all_bound comps"
      ; mkstr "[In %s comps]" xch_chan
      ; "(tr ~~ [KInvariant kst])"
      ]
  in
  let pacc = coq_of_prog k tr fr tprog.program in
  lcat
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
      mkstr "pose (%s := %s kst);" id id)
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
      lcat
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
  pose (comps := components kst);
  pose (tr := ktr kst);
%s
  refine (
    req <- recv_msg c
    (tr ~~~ expand_ktrace tr)
    <@> [In c comps] * %s * all_bound_drop comps c * (tr ~~ [KInvariant kst]);

    match req with
%s
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ KRecv c (BadTag tag) :: tr) %s) }}
    end
  );  sep unfoldr simplr.
Qed.
"
  comp var_ext (fields_in_comps_fr spec) hands kstate_vars

let coq_of_init k =
  let pacc = coq_of_prog k "tr" [] k.init in
  lcat
    [ "let tr := inhabits nil in"
    ; pacc.code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        (String.concat "" (List.map (mkstr "%s :: ") pacc.comps))
        pacc.trace_impl
        (lkup_st_fields pacc.sstate k)
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

(*
  let kstate_vars =
    s.var_decls |> List.map fst |> String.concat " "
  in
*)

let subs s =
  let (xch_chan, exchanges) = s.exchange in
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "KTRACE_VAR_DECLS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "let %s := (%s s) in\n" id id)))
  ; "KTRACE_VAR_LISTS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ; "VE_STATE_VAR_DECLS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "Let %s := (%s s).\n" id id)))
  ; "VE_STATE_VAR_LISTS",
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ; "VE_HANDLED_CASES",
      fmt exchanges (fun (comp, handlers) ->
        fmt handlers (fun h ->
          h.responds
            |> List.fold_left
                (fun (i, conds, res) cprog ->
                  ( i + 1
                  , cprog.condition :: conds
                  , coq_spec_of_handler s comp xch_chan h.trigger conds i cprog :: res
                  ))
                (0, [], [])
            |> fun (_, _, res) -> res
            |> String.concat "\n"
        )
      )
  ; "VE_UNHANDLED_CASES",
      fmt s.components (fun (comp, _) ->
        let handlers =
          try List.assoc comp exchanges
          with Not_found -> []
        in
        let handled m =
          List.exists (fun h -> h.trigger.tag = m.tag) handlers
        in
        let unhandled_msgs =
          List.filter (fun m -> not (handled m)) s.msg_decls
        in
        fmt unhandled_msgs (fun m ->
          let args = String.concat " " (List.map coq_of_typ m.payload) in
          lcat
            [ mkstr "| VE_%s_%s:" comp m.tag
            ; mkstr "  forall %s %s," args xch_chan
            ;       "  ValidExchange (mkst"
            ; mkstr "    comps"
            ; mkstr "    (tr ~~~ KRecv %s (%s %s) :: tr)" xch_chan m.tag args
            ;       fmt s.var_decls fst
            ;       "  )"
            ]
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
  ; "KSTATE_FIELDS",
      fmt s.var_decls (fun (id, typ) ->
        mkstr "; %s : %s" id (coq_of_typ typ))
  ; "KSTATE_INVS",
      (* WARNING very similar to fields_in_comps_fr *)
      (* require all chan state fields to be in the state components *)
      s.var_decls
        |> List.filter (fun (_, typ) -> typ = Chan)
        |> List.map (fun (id, _) -> mkstr "* [In (%s s) (components s)]" id)
        |> String.concat "\n"

  ; "INIT_CODE",
      coq_of_init s
  ; "EXCHANGES",
      fmt s.components (fun (comp, _) ->
        coq_of_exchange s xch_chan comp)
  ; "TYPE_OF_COMP_DEFAULT",
      mkstr "\n| nil => %s (* TODO: need default or proof *)"
        (fst (List.hd s.components))
  ; "KBODY", (
      let comp_xch =
        s.components
          |> List.map (fun (c, _) -> mkstr "\n| %s => exchange_%s" c c)
          |> String.concat ""
      in
      mkstr "
  intros kst.
  pose (comps := components kst);
  pose (tr := ktr kst);
  %s
  refine (
    comp <- select comps
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [KInvariant kst] * all_bound comps * %s);
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
      (fmt s.var_decls (fun (id,typ) -> (mkstr "pose (%s := %s kst);" id id)))
      (fields_in_comps_fr s)
      comp_xch
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id))))
  ; "PROPERTIES",
      fmt s.props coq_of_prop
  ]
