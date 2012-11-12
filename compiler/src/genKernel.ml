open Common
open Kernel
open Gen

let lkup_var st id =
  try
    List.assoc id st
  with Not_found ->
    Var id

let rec lkup_expr st = function
  | Var id            -> lkup_var st id
  | NumLit i          -> NumLit i
  | StrLit s          -> StrLit s
  | Plus (a, b)       -> Plus (lkup_expr st a, lkup_expr st b)
  | CompFld (c, f)    -> CompFld (c, f)
  | FunCall (f, args) -> FunCall (f, List.map (lkup_expr st) args)

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
  { code         : string
  ; frame        : string list
  ; comps        : string list
  ; trace_impl   : string
  ; trace_spec   : string
  (* sstate now contains mappings from a chan name occurence to the fresh name
  of that same chan, in the case where is has been shadowed. The type could be
  simplified as this does not deal anymore with other types of expressions,
  whose let bindings are expanded after parsing, but I leveraged the existing
  sstate code for simplicity. *)
  ; sstate       : sstate
  (* scoped_chans keeps track of the channel names in scope, so that a binding
  which shadows a scoped chan can be detected. *)
  ; scoped_chans : string list
  (* fresh_vars keeps track of all the chan names introduced for disambiguating
  shadowing, so that these can be quantified in places where it's needed. *)
  ; fresh_vars   : string list
  }

let coq_of_cmd k pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^
          (
            let c = coq_of_expr (lkup_var pacc.sstate c) in
            let fr' = extract_bound c pacc.frame in
            mkstr "
send_msg %s %s
(tr ~~~ expand_ktrace (%s))
<@> %s;;
"
              c (coq_of_msg_expr m)
              pacc.trace_impl (coq_of_frame fr'))
      ; trace_impl =
          mkstr "KSend %s %s :: %s"
            (coq_of_expr (lkup_var pacc.sstate c))
            (coq_of_msg_expr m) pacc.trace_impl
      ; trace_spec =
          mkstr "KSend %s %s :: %s"
            (coq_of_expr (lkup_var pacc.sstate c))
            (coq_of_msg_expr m) pacc.trace_spec
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
            (coq_of_expr f)
            (coq_of_expr arg)
            res pacc.trace_spec
      }
  | Spawn (res, (comp, fields)) ->
      let (path, _) = List.assoc comp k.components in
      let is_shadowing = List.mem res pacc.scoped_chans in
      let fresh = mkstr "%s_%d" res (tock ()) in
      let bind_fresh = mkstr "let %s := %s in\n" fresh res in
      let patched_frame =
        if is_shadowing then
          List.map (Str.global_replace (Str.regexp res) fresh) pacc.frame
        else
          pacc.frame
      in
      { code = pacc.code ^
          mkstr "
%s%s <- exec %s (str_of_string \"%s\") (%s)
(tr ~~~ expand_ktrace (%s))
<@> %s;
"
            (if is_shadowing then bind_fresh else "")
            fresh comp path
            (mkstr "Build_st_%s %s" comp
              (String.concat " " (List.map coq_of_expr fields))
            )
            pacc.trace_impl
            (coq_of_frame patched_frame)
      ; trace_impl =
          mkstr "KExec (str_of_string \"%s\") %s :: %s"
            path fresh pacc.trace_impl
      ; trace_spec =
          mkstr "KExec (str_of_string \"%s\") %s :: %s"
            path fresh pacc.trace_spec
      ; frame =
          mkstr "bound %s" fresh :: patched_frame
      ; comps =
          fresh :: pacc.comps
      ; sstate =
          set_var pacc.sstate res (Var fresh)
      ; scoped_chans =
          fresh :: pacc.scoped_chans
      ; fresh_vars =
          fresh :: pacc.fresh_vars
      }
  | Assign (_, _) -> failwith "Assigns should have been desugared"

let coq_of_prog s tr0 fr0 p sc ss =
  let rec loop pacc = function
    | Nop ->
        { pacc with code = pacc.code ^ "\n(* Nop *)\n" }
    | Seq (c, p') ->
        loop (coq_of_cmd s pacc c) p'
  in
  let pacc0 =
    { code         = ""
    ; frame        = fr0
    ; comps        = []
    ; trace_impl   = tr0
    ; trace_spec   = tr0
    ; sstate       = ss
    ; scoped_chans = sc
    ; fresh_vars   = []
    }
  in
  loop pacc0 p

let coq_trace_spec_of_prog s fr p sc ss =
  (coq_of_prog s "" fr p sc ss).trace_spec

let coq_trace_impl_of_prog s fr p sc ss =
  (coq_of_prog s "" fr p sc ss).trace_impl

let rec expr_vars = function
  | Var id -> [id]
  | Plus (e1, e2) -> expr_vars e1 @ expr_vars e2
  | _ -> []

(* vars that need forall binding *)
let cmd_vars pacc = function
  | Send (c, m) ->
      (coq_of_expr (lkup_var pacc.sstate c))
      :: List.flatten (List.map expr_vars m.payload)
  | Call (var, _, arg) ->
      var :: expr_vars arg
  | Spawn (res, _) ->
      [(coq_of_expr (lkup_var pacc.sstate res))]
  | Assign (_, _) ->
      [] (* will be bound by a let *)

let rec prog_vars pacc = function
  | Nop -> []
  | Seq (c, p) -> cmd_vars pacc c @ prog_vars pacc p

let coq_of_msg_pat m =
  mkstr "| %s %s =>" m.tag
    (String.concat " " m.payload)

let handler_vars pacc xch_chan trig prog =
  uniq (xch_chan :: trig.payload @ prog_vars pacc prog)

(* handler vars modulo global state vars *)
let handler_vars_nonstate pacc xch_chan trig prog svars =
  let globals =
    List.map (fun (id, _) -> id) svars
  in
  List.filter
    (fun x -> not (List.mem x globals))
    (handler_vars pacc xch_chan trig prog)

let coq_of_cond_prop = function
  | Always            -> "True"
  | NumEq (id, i)     -> mkstr "(nat_of_num %s = %d)" id i
  | ChanEq (idl, idr) -> mkstr "(%s = %s)" idl idr
  | StrEq (l, r)      -> mkstr "(%s = %s)" (coq_of_expr l) (coq_of_expr r)

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

let coq_spec_of_handler k comp xch_chan trig conds index cprog =
  let (prog, _) = cprog.program in
  let fr0 =
    List.map
      (fun c -> mkstr "bound %s" c)
      (xch_chan :: chans_of_prog prog)
  in
  let scoped_chans =
    List.map fst (List.filter (fun (_, typ) -> typ = Chan) k.var_decls)
  in
  let pacc = coq_of_prog k "" fr0 prog scoped_chans [] in
  lcat
    [ mkstr "| VE_%s_%s_%d :"
        comp trig.tag index
    ; mkstr "forall %s (CT : projT1 %s = %s),"
        (String.concat " " (handler_vars_nonstate pacc xch_chan trig prog k.var_decls))
        xch_chan comp
    ; coq_of_cond_spec conds cprog.condition
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
  | ChanEq (idl, idr) ->
      lcat
        [ if index > 0 then " else " else ""
        ; mkstr "if (tchan_eq %s %s) then" idl idr
        ]
  | StrEq (l, r) ->
      lcat
        [ if index > 0 then " else " else ""
        ; mkstr "if (list_eq_dec ascii_dec %s %s) then"
            (coq_of_expr l) (coq_of_expr r)
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
  let (prog, _) = tprog.program in
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
  let pacc = coq_of_prog k tr fr prog [] [] in
  lcat
    [ coq_of_cond index tprog.condition ^ " ("
    ; pacc.code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s) %s) }}"
        (String.concat "" (List.map (mkstr "%s :: ") pacc.comps))
        pacc.trace_impl
        (lkup_st_fields pacc.sstate k)
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
    ; responds = [{condition = Always; program = (Nop, [])}]
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
  lcat
    [ mkstr "Definition exchange_%s :" comp
    ; mkstr "  forall (%s : tchan) (CT : projT1 %s = %s) (kst : kstate),"
        xch_chan xch_chan comp
    ; mkstr "  STsep (kstate_inv kst * [In %s (components kst)])" xch_chan
    ; mkstr "        (fun (kst' : kstate) => kstate_inv kst')."
    ; mkstr "Proof."
    ; mkstr "  intros %s CT kst;" xch_chan
    ; mkstr "  pose (comps := components kst);"
    ; mkstr "  pose (tr := ktr kst);"
    ; mkstr "%s" var_ext
    ; mkstr "  refine ("
    ; mkstr "    req <- recv_msg %s" xch_chan
    ; mkstr "    (tr ~~~ expand_ktrace tr)"
    ; mkstr "    <@> [In %s comps] * %s * all_bound_drop comps %s * (tr ~~ [KInvariant kst]);"
              xch_chan (fields_in_comps_fr spec) xch_chan
    ; mkstr ""
    ; mkstr "    match req with"
    ; mkstr "%s" hands
    ; mkstr "    (* special case for errors *)"
    ; mkstr "    | BadTag tag =>"
    ; mkstr "      {{ Return (mkst comps (tr ~~~ KRecv %s (BadTag tag) :: tr) %s) }}"
              xch_chan kstate_vars
    ; mkstr "    end"
    ; mkstr "  );  sep unfoldr simplr."
    ; mkstr "Qed."
    ]

let coq_of_init k =
  let (init, sstate) = k.init in
  let pacc = coq_of_prog k "tr" [] init [] sstate in
  lcat
    [ "let tr := inhabits nil in"
    ; pacc.code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        (String.concat "" (List.map (mkstr "%s :: ") pacc.comps))
        pacc.trace_impl
        (lkup_st_fields pacc.sstate k)
    ]

let subs k =
  let (xch_chan, exchanges) = k.exchange in
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "KTRACE_VAR_DECLS",
      (fmt k.var_decls (fun (id, _) -> (mkstr "let %s := %s s in\n" id id)))
  ; "KTRACE_VAR_LISTS",
      (fmt k.var_decls (fun (id, _) -> (mkstr "%s " id)))
  ; "VE_STATE_VAR_DECLS",
      (fmt k.var_decls (fun (id, _) -> (mkstr "Let %s := %s s.\n" id id)))
  ; "VE_STATE_VAR_LISTS",
      (fmt k.var_decls (fun (id, _) -> (mkstr "%s " id)))
  ; "VE_HANDLED_CASES",
      fmt exchanges (fun (comp, handlers) ->
        fmt handlers (fun h ->
          h.responds
            |> List.fold_left
                (fun (i, conds, res) cprog ->
                  ( i + 1
                  , cprog.condition :: conds
                  , coq_spec_of_handler k comp xch_chan h.trigger conds i cprog :: res
                  ))
                (0, [], [])
            |> fun (_, _, res) -> res
            |> String.concat "\n"
        )
      )
  ; "VE_UNHANDLED_CASES",
      fmt k.components (fun (comp, _) ->
        let handlers =
          try List.assoc comp exchanges
          with Not_found -> []
        in
        let handled m =
          List.exists (fun h -> h.trigger.tag = m.tag) handlers
        in
        let unhandled_msgs =
          List.filter (fun m -> not (handled m)) k.msg_decls
        in
        fmt unhandled_msgs (fun m ->
          let args =
            m.payload
              |> mapi (fun i p -> mkstr "%s_%d" (coq_of_typ p) i)
              |> String.concat " "
          in
          lcat
            [ mkstr "| VE_%s_%s:" comp m.tag
            ; mkstr "  forall %s %s," args xch_chan
            ;       "  ValidExchange (mkst"
            ; mkstr "    comps"
            ; mkstr "    (tr ~~~ KRecv %s (%s %s) :: tr)" xch_chan m.tag args
            ;       fmt k.var_decls fst
            ;       "  )"
            ]
        )
      )
  ; "VE_SOLVE_TAC",
      fmt k.components (fun (comp, _) ->
        let hprogs m =
          try
            let hs = List.assoc comp exchanges in
            let h  = List.find (fun h -> h.trigger.tag = m.tag) hs in
            h.responds
          with Not_found ->
            []
        in
        fmt k.msg_decls (fun m ->
          let hs = hprogs m in
          match hs with
          | [] ->
              mkstr "    | eapply VE_%s_%s; eauto" comp m.tag
          | _  ->
              lcat (mapi (fun i _ ->
                mkstr "    | eapply VE_%s_%s_%d; eauto" comp m.tag i) hs)
        )
      )
  ; "KTRACE_INIT", (
      let (init, sstate) = k.init in
      let pacc = coq_of_prog k "" [] init [] sstate in
      mkstr "forall %s,\nKInvariant (mkst (%snil) [%snil] %s)"
        (String.concat " " pacc.fresh_vars)
        (String.concat "" (List.map (fun c -> mkstr "%s :: " c) pacc.comps))
        pacc.trace_impl (* TODO should this use trace_spec ? *)
        (lkup_st_fields pacc.sstate k)
    )
  ; "KSTATE_FIELDS",
      fmt k.var_decls (fun (id, typ) ->
        mkstr "; %s : %s" id (coq_of_typ typ))
  ; "KSTATE_INVS",
      (* WARNING very similar to fields_in_comps_fr *)
      (* require all chan state fields to be in the state components *)
      k.var_decls
        |> List.filter (fun (_, typ) -> typ = Chan)
        |> List.map (fun (id, _) -> mkstr "* [In (%s s) (components s)]" id)
        |> String.concat "\n"

  ; "INIT_CODE",
      coq_of_init k
  ; "EXCHANGES",
      fmt k.components (fun (comp, _) ->
        coq_of_exchange k xch_chan comp)
  ; "TYPE_OF_COMP_DEFAULT",
      mkstr "\n| nil => %s (* TODO: need default or proof *)"
        (fst (List.hd k.components))
  ; "KBODY", (
      let comp_xch =
        k.components
          |> List.map (fun (c, _) ->
               mkstr "| %s => fun _ => exchange_%s comp _" c c)
          |> String.concat "\n"
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
      let p := projT1 comp in
      match p as p' return p = p' -> _ with
%s
      end
    ) in
    s' <- handler _ (mkst comps (tr ~~~ KSelect comps comp :: tr) %s);
    {{ Return s' }}
  );
  sep unfoldr simplr.
"
      (fmt k.var_decls (fun (id, _) -> (mkstr "pose (%s := %s kst);" id id)))
      (fields_in_comps_fr k)
      comp_xch
      (fmt k.var_decls (fun (id, _) -> (mkstr "%s " id))))
  ]
