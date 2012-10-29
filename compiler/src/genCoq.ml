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

let mk_buffer () =
  let b = Buffer.create 16 in
  (Buffer.add_string b, fun () -> Buffer.contents b)

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

(* eftable : a state variable name -> an expressions containing the
current value of the variable represented by the old variables at the
start of the handler. (e.g, after a := a + 1, a is mapped to a + 1 *)
let rec get_affected_expr eftable id =
  match eftable with
  | [] -> Var id
  | (id', ex) :: eftable' ->
      if id = id' then ex else (get_affected_expr eftable' id)

let rec coq_of_expr_for_trace eftable = function
  | Var id -> (coq_of_expr (get_affected_expr eftable id))
  | NumLit i -> coq_of_num i
  | StrLit s -> coq_of_string s
  | Plus(a, b) ->
    mkstr "(num_of_nat ((nat_of_num (%s)) + (nat_of_num (%s))))"
      (coq_of_expr_for_trace eftable a) (coq_of_expr_for_trace eftable b)

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

let coq_of_msg_expr_for_trace eftable m =
  mkstr "(%s %s)" m.tag
    (if (List.length m.payload = 0) then " " else
    (m.payload
      |> List.map (coq_of_expr_for_trace eftable)
      |> String.concat ") ("
      |> mkstr "(%s)"))

let coq_of_msg_expr m =
    mkstr "(%s%s)" m.tag
      (
        match m.payload with
        | [] -> ""
        | pl ->
          pl
          |> List.map coq_of_expr
          |> String.concat ") ("
          |> mkstr " (%s)"
      )

let coq_of_frame fr =
  fr |> List.map (mkstr "%s * ")
     |> String.concat ""
     |> mkstr "%semp"

type prog_acc =
  { code  : string
  ; trace_impl : string
  ; trace_spec : string
  ; frame : string list
  ; comps : string list
  ; effecttbl : (string * expr) list
  }

let fresh_chan_id () =
  mkstr "c%d" (tock ())


let rec subst e table =
  match e with
  | Var id ->
      let (id', ex) = (List.find (fun (id', ex) -> id = id') table) in
      ex
  | Plus (e1, e2) ->
      Plus ((subst e1 table), (subst e2 table))
  | _ -> e

let apply_effect id expr effecttbl =
  (* working *)
  (id,(subst expr effecttbl)) :: effecttbl


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

let coq_of_cmd s pacc = function
  | Send (c, m) ->
      {
        pacc with code = pacc.code ^
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
            c (coq_of_msg_expr_for_trace pacc.effecttbl m) pacc.trace_spec

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
            (coq_of_expr f) (coq_of_expr arg) res pacc.trace_impl
      ; trace_spec =
          mkstr "Call_t %s %s %s ++ %s"
            (coq_of_expr_for_trace pacc.effecttbl f) (coq_of_expr_for_trace pacc.effecttbl arg) res pacc.trace_spec
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
      ; effecttbl = pacc.effecttbl
      }
  | Assign (id, expr) ->
      {
         code = (
         let (add, contents) = mk_buffer () in
         add pacc.code;
         add (mkstr "
let %s := %s in" id (coq_of_expr expr));
         contents ()
         );
     trace_spec = pacc.trace_spec
     ; trace_impl = pacc.trace_impl
     ; frame = pacc.frame
     ; comps = pacc.comps
     ; effecttbl = (apply_effect id expr pacc.effecttbl)
      }


let init_effecttbl vardecls =
  (List.fold_left
    (fun acc (id, typ) ->
      (id, (Var id)) :: acc)
     [] vardecls)

let coq_of_prog s tr0 fr0 p =
  let rec loop pacc = function
    | Nop -> pacc
    | Seq (c, p') -> loop (coq_of_cmd s pacc c) p'
  in
  loop {code = ""; trace_impl = tr0; trace_spec = tr0; frame = fr0; comps = []; effecttbl = (init_effecttbl s.var_decls)} p

let coq_trace_spec_of_prog s fr p =
  (coq_of_prog s "" fr p).trace_spec

let coq_trace_impl_of_prog s fr p =
  (coq_of_prog s "" fr p).trace_impl

let effects_of_prog s fr p =
  (coq_of_prog s "" fr p).effecttbl

let expr_vars = function
  | Var id -> [id]
  | _ -> []

let cmd_vars = function
  | Send (c, m) ->
      c :: List.flatten (List.map expr_vars m.payload)
  | Call (var, func, arg) ->
      var :: expr_vars arg
  | Assign (id, expr) ->
      []
  |  _ -> []
  (*
  we have to consider this separately
  | Spawn (res, path) ->
      [res]
  *)

let comp_cmd_vars = function
  | Spawn (res, path) ->
      [res]
  |  _ -> []

let rec init_vars = function
  | Nop -> []
  | Seq (c, p) -> cmd_vars c @ init_vars p

let rec comp_vars = function
  | Nop -> []
  | Seq (c, p) -> (comp_vars p) @ (comp_cmd_vars c)

let coq_of_msg_pat m =
  mkstr "| %s %s =>" m.tag
    (String.concat " " m.payload)


(* we have to excluse global state variables here for forall of each
handlers *)
let handler_vars xch_chan trig statevars program =
  let varnames = (List.map (fun (id,typ) -> id) statevars) in
  (List.fold_left
    (fun lst elem ->
      if List.mem elem varnames then lst
      else (elem :: lst)
    ) [] (uniq ((xch_chan :: trig.payload) @ (comp_vars program) @ (init_vars program))))

let coq_mkst_with_effects effecttbl vardecls =
  (fmt vardecls (fun (id, typ) ->
    (mkstr "( %s )" (coq_of_expr (get_affected_expr effecttbl id)))))

let rec get_init_state_values cmds =
  match cmds with
  | c :: cmds' ->
      (let res = (get_init_state_values cmds') in
      (match c with
      | Assign (id, e) -> ((id, e) :: res)
      | Spawn (id, e) -> ((id, Var id) :: res)
      | _ -> res))
  | [] -> []

let rec ext_cmds prog =
  match prog with
  | Nop -> []
  | Seq (cmd, prog') -> cmd :: (ext_cmds prog')

let coq_init_mkst prog vardecls =
  let cmds = (ext_cmds prog) in
  let vals = get_init_state_values cmds in
  mkstr " %s "
    (fmt vardecls (fun (id, typ) ->
      (mkstr "( %s )" (coq_of_expr (snd (try List.find (fun (id', e) -> id = id') vals with Not_found -> print_string id; print_string " not found\n"; raise Not_found))))))

let coq_of_logical le =
  match le with
  | LogEq (id, v) ->
      (mkstr "(nat_of_num %s) = %d" id v)


let coq_of_condition_spec conds cond =
  let conds_str =
    (String.concat " -> " (List.map (fun cond ->
    match cond with
    | None -> ""
    | Some le -> mkstr "~(%s)" (coq_of_logical le)) conds)) in
  let res = (match cond with
  | None -> conds_str
  | Some le -> (mkstr " %s %s "
    (if conds_str = "" then "" else (mkstr " %s -> " conds_str))
    (coq_of_logical le))
  ) in
  (if res = "" then "" else (mkstr " %s -> " res))


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
  let rec chans_of_prog_aux accu = function
  | Nop -> ChanSet.elements accu
  | Seq(cmd, rest) ->
    let accu = ChanSet.union accu (chans_of_cmd cmd) in
    chans_of_prog_aux accu rest
  in
  chans_of_prog_aux ChanSet.empty p


let coq_spec_of_handler s comp xch_chan trig conds index tprog =
  let fr = List.map (fun c -> mkstr "bound %s" c) (xch_chan :: chans_of_prog tprog.program) in
  let effecttbl = effects_of_prog s fr tprog.program in
  let comp_vs =  (comp_vars tprog.program) in
  let hdr =
    mkstr "
| VE_%s_%s_%d : \nforall %s, %s \nValidExchange (mkst (%s) "
      comp
      trig.tag
      index
      (String.concat " " ((handler_vars xch_chan trig s.var_decls tprog.program)))
      (coq_of_condition_spec conds tprog.condition)
      (match comp_vs with | [] -> "comps" | _ -> mkstr "%s::comps" (String.concat "::" (comp_vs)))
  in
  let tr =
    if tprog.program = Nop then
      "      (* no response *)"
    else
      (* let fr = [ mkstr "bound %s" xch_chan ] in *)
      coq_trace_spec_of_prog s fr tprog.program
  in
  let ftr =
    mkstr "(tr ~~~ ((%s RecvMsg %s (%s %s)) ++ tr))"
      tr
      xch_chan
      trig.tag
      (String.concat " " trig.payload)
  in
  let other_state = (coq_mkst_with_effects effecttbl s.var_decls) in
  (lines [hdr; ftr; other_state; ")"])


let coq_of_init s =
  let cp = coq_of_prog s "tr" [] s.init in
  lines
    [ "let tr := inhabits nil in"
    ; if cp.code = ""
      then "        (* no code *)"
      else cp.code
    ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s) %s) }}"
        (cp.comps |> List.map (mkstr "%s :: ") |> String.concat "")
        cp.trace_impl
        (coq_init_mkst s.init s.var_decls)
    ]


let coq_of_handler_header trig=
  coq_of_msg_pat trig

let coq_of_condition index cond =
  match cond with
  | None ->
      (if index = 0 then "" else " else ")
  | Some le ->
      match le with
      | LogEq (id, v) ->
        lines
          [ (if index > 0 then " else " else "");
            (mkstr "if (Peano_dec.eq_nat_dec (nat_of_num %s) %d) then " id v);
          ]

let frames_of_vars s =
  s.var_decls
  |> List.filter (fun (_, typ) -> typ = Chan)
  |> List.map (fun (id, _) -> mkstr "[In %s comps]" id)

let coq_of_handler s xch_chan trig index tprog =
  let tr =
    mkstr "RecvMsg %s (%s %s) ++ tr"
      xch_chan
      trig.tag
      (String.concat " " trig.payload)
  in
  let fr = (
    let chans = chans_of_prog tprog.program in
    let acc0 =
      [ "all_bound comps"
      ; mkstr "[In %s comps]" xch_chan
      ; "(tr ~~ [KInvariant kst])"
      ]
    in
    (frames_of_vars s) @ acc0
  )
  in
  let pacc = coq_of_prog s tr fr tprog.program in
  lines
    [
    (*coq_of_msg_pat trig
    ;  *)
    coq_of_condition index tprog.condition
    ; " ( ";
    if pacc.code = "" then
        "        (* no code *)"
      else
        pacc.code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s) %s) }}"
        (pacc.comps |> List.map (mkstr "%s :: ") |> String.concat "")
        pacc.trace_impl
        (s.var_decls |> List.map fst |> String.concat " ")
     ;" ) "
    ]

let coq_of_exchange spec xch_chan comp =
  (* here's where the when has be generated *)
  let kstate_vars =
    spec.var_decls |> List.map fst |> String.concat " "
  in
  let var_ext =
    (fmt spec.var_decls (fun (id,typ) -> (mkstr "pose (%s := (%s kst));" id id)))
  in
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
      let constr = mkstr "%s %s" msg.tag (str_of_args msg) in
      let unhandled = Printf.sprintf "
    (* not handled *)
    | %s =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c (%s) ++ tr) %s) }}
"
        constr constr kstate_vars
      in
      match comp_handlers with
      | None -> unhandled
      | Some(exchanges) ->
        try (
          let h =
            List.find (fun h -> h.trigger.tag = msg.tag) (snd exchanges)
          in
        lines
        [ coq_of_handler_header h.trigger ;
          fmti h.responds (coq_of_handler spec xch_chan h.trigger)
        ]
       (* coq_of_handler spec xch_chan handler *)
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
  intros c kst;
  pose (comps := (components kst));
  pose (tr := (ktr kst));
%s
  refine (
    req <- recv_msg c tr
    <@> [In c comps]%s * all_bound_drop comps c * (tr ~~ [KInvariant kst]);
    match req with
%s
    (* special case for errors *)
    | BadTag tag =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c (BadTag tag) ++ tr) %s) }}
    end
  );  sep unfoldr simplr.
Qed.
"
  comp var_ext vars_frames hands kstate_vars


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
          (* fmti h.responds (coq_spec_of_handler s comp xch_chan h.trigger) *)
      )
        (* fmt handlers (coq_spec_of_handler s comp xch_chan)) *)
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
      let t = coq_trace_impl_of_prog s [] s.init in
      let comp_vs = comp_vars s.init in
      let init_vs = init_vars s.init in
      let mkst = coq_init_mkst s.init s.var_decls in
      (match (comp_vs @ init_vs) with
      | [] -> "" (* ignore this case. What's the kernel for without any component? *)
      | _  -> mkstr "forall %s, KInvariant (mkst (%s) [%s nil] %s) "
          (String.concat " " (comp_vs @ init_vs))
          (mkstr "%s::nil" (String.concat "::" (comp_vs)))
          t
          mkst
      )
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
      let kstate_invs =
        match frames_of_vars s with
        | [] -> ""
        | l  -> " * " ^ String.concat " * " l
      in
      mkstr "
  intros kst.
  pose (comps := (components kst));
  pose (tr := (ktr kst));
  %s
  refine (
    comp <- select comps tr
    <@> (tr ~~ [KInvariant kst] * all_bound comps%s);
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
      kstate_invs
      comp_xch
      (fmt s.var_decls (fun (id,typ) -> (mkstr "%s " id)))
  ]
