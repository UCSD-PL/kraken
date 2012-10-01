open Common
open Kernel

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

let coq_of_expr = function
  | Var id -> id
  | NumLit i -> coq_of_num i
  | StrLit s -> coq_of_string s

let coq_of_constant_decl (id, e) =
  mkstr "Definition %s := %s." id (coq_of_expr e)

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
        |> String.concat "\n"
  in
  let tag =
    mkstr "RecvNum c (Num \"%03d\")"
      (List.assoc m.tag tag_map)
  in
  String.concat "\n" [hdr; pay; tag]

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
        |> String.concat "\n"
  in
  let tag =
    mkstr "SendNum c (Num \"%03d\")"
      (List.assoc m.tag tag_map)
  in
  String.concat "\n" [hdr; pay; tag]

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
      |> String.concat "\n\n"
  in
  let ret =
    mkstr "{{ Return (%s %s) }}\n" m.tag (str_of_args m)
  in
  String.concat "\n\n" [hdr; pay; ret]

(* send msg on bound chan "c" *)
(* WARNING copy/paste of coq_recv_msg *)
let coq_send_msg tag_map m =
  let hdr =
    String.concat "\n\n"
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
      |> String.concat "\n\n"
  in
  let ret =
    "{{ Return tt }}\n"
  in
  String.concat "\n\n" [hdr; pay; ret]

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

let coq_of_cmd pacc = function
  | Send (c, m) ->
      { pacc with code = pacc.code ^ "\n\n" ^
          (let fr' = remove (mkstr "bound %s" c) pacc.frame in
          mkstr "send_msg %s %s\n(tr ~~~ %s)\n<@> %s;;"
            c (coq_of_msg_expr m)
            pacc.trace (coq_of_frame fr'))
      ; trace =
          mkstr "SendMsg %s %s ++ %s"
            c (coq_of_msg_expr m) pacc.trace
      }
  | Call (res, f, arg) ->
      { pacc with code = pacc.code ^ "\n\n" ^
          mkstr "%s <- call %s %s\n(tr ~~~ %s)\n<@> %s;"
            res (coq_of_expr f) (coq_of_expr arg)
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "Call_t %s %s %s ++ %s"
            (coq_of_expr f) (coq_of_expr arg) res pacc.trace
      }
  | Spawn (res, path) ->
      { code = pacc.code ^ "\n\n" ^
          mkstr "%s <- exec %s\n(tr ~~~ %s)\n<@> %s;"
            res (coq_of_expr path)
            pacc.trace (coq_of_frame pacc.frame)
      ; trace =
          mkstr "Exec_t %s %s ++ %s"
            (coq_of_expr path) res pacc.trace
      ; frame =
          mkstr "bound %s" res :: pacc.frame
      ; comps =
          res :: pacc.comps
      }

let coq_of_prog tr0 fr0 p =
  let rec loop pacc = function
    | Nop -> pacc
    | Seq (c, p') -> loop (coq_of_cmd pacc c) p'
  in
  loop {code = ""; trace = tr0; frame = fr0; comps = []} p

let coq_trace_of_prog fr p =
  (coq_of_prog "" fr p).trace

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

let rec prog_vars = function
  | Nop -> []
  | Seq (c, p) -> cmd_vars c @ prog_vars p

let coq_of_msg_pat m =
  mkstr "| %s %s =>" m.tag
    (String.concat " " m.payload)

let handler_vars xch_chan h =
  uniq (xch_chan :: h.trigger.payload @ prog_vars h.respond)

let coq_spec_of_handler xch_chan h =
  let hdr =
    mkstr "| VE_%s :\nforall %s,\nValidExchange ("
      h.trigger.tag
      (String.concat " " (handler_vars xch_chan h))
  in
  let bdy =
    if h.respond = Nop then
      "      (* no response *)"
    else
      let fr = [ mkstr "bound %s" xch_chan ] in
      coq_trace_of_prog fr h.respond
  in
  let ftr =
    mkstr "RecvMsg %s (%s %s))"
      xch_chan
      h.trigger.tag
      (String.concat " " h.trigger.payload)
  in
  String.concat "\n" [hdr; bdy; ftr]

let coq_of_init init =
  let cp = coq_of_prog "tr" [] init in
  String.concat "\n\n"
  [ "let tr := inhabits nil in"
  ; if cp.code = ""
    then "        (* no code *)"
    else cp.code
  ; mkstr "{{ Return (mkst (%snil) (tr ~~~ %s)) }}"
      (cp.comps |> List.map (mkstr "%s :: ") |> String.concat "")
      cp.trace
  ]

let coq_of_handler xch_chan h =
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
  let pacc = coq_of_prog tr fr h.respond in
  String.concat "\n\n"
    [ coq_of_msg_pat h.trigger
    ; if pacc.code = "" then
        "        (* no code *)"
      else
        pacc.code
    ; mkstr "{{ Return (mkst (%scomps) (tr ~~~ %s)) }}"
        (pacc.comps |> List.map (mkstr "%s :: ") |> String.concat "")
        pacc.trace
    ]

(* coq template has string holes for
 *  0. constants
 *  1. declaring msg
 *  2. RecvMsg cases
 *  3. SendMsg cases
 *  4. recv_msg cases
 *  5. send_msg cases
 *  6. ValidExchange cases
 *  7. exchange channel name
 *  8. exchange cases
 *)
let coq_template = format_of_string "
Require Import List.
Require Import Ascii.
Require Import Ynot.
Require Import KrakenBase.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

(* constants *)
%s

Inductive msg : Set :=
%s
(* special case for errors *)
| BadTag : num -> msg.

Definition RecvMsg (c : chan) (m : msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      RecvNum c p0
  end.

Definition SendMsg (c : chan) (m : msg) : Trace :=
  match m with
%s
    (* special case for errors *)
    | BadTag p0 =>
      SendNum c (Num \"000\")
  end.

Definition recv_msg :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m : msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recv_num c tr;
    match tag with
%s
      (* special case for errors *)
      | m =>
        {{ Return (BadTag m) }}
    end
  );
  sep fail auto;
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.

Definition send_msg :
  forall (c : chan) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    match m with
%s
      (* special case for errors *)
      | BadTag _ =>
        send_num c (Num \"000\") tr;;
        {{ Return tt }}
    end
  );
  sep fail auto;
  repeat rewrite app_ass; simpl;
  sep fail auto.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvMsg SendMsg.

Inductive ValidExchange : Trace -> Prop :=
%s
(* special case for errors *)
| VE_BadTag :
  forall c tag,
  ValidExchange (
    RecvMsg c (BadTag tag)).

Inductive AddedValidExchange : Trace -> Trace -> Prop :=
| AVE_intro :
  forall tr1 tr2,
  ValidExchange tr2 ->
  AddedValidExchange tr1 (tr2 ++ tr1).

Inductive KTrace : Trace -> Prop :=
| KT_init :
  %s
| KT_select :
  forall tr cs c,
  KTrace tr ->
  KTrace (Select cs c :: tr)
| KT_exchange :
  forall tr1 tr2,
  KTrace tr1 ->
  AddedValidExchange tr1 tr2 ->
  KTrace tr2.

Hint Constructors KTrace.

Fixpoint all_bound (cs : list chan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' => bound c * all_bound cs'
  end.

(* all cs bound except _first_ occurrence of drop *)
Fixpoint all_bound_drop (cs : list chan) (drop : chan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' =>
      if chan_eq c drop then
        all_bound cs'
      else
        bound c * all_bound_drop cs' drop
  end.

Lemma unpack_all_bound :
  forall cs c,
  In c cs ->
  all_bound cs ==> bound c * all_bound_drop cs c.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite chan_eq_true. apply himp_refl.
  case (chan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_bound :
  forall cs c,
  In c cs ->
  bound c * all_bound_drop cs c ==> all_bound cs.
Proof.
  induction cs; simpl; intros. contradiction.
  destruct H; subst. rewrite chan_eq_true. apply himp_refl.
  case (chan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in
  traced tr * [KTrace tr] * all_bound (components s).

Ltac unfoldr := unfold kstate_inv.

Ltac simplr_fail :=
  match goal with
  | [ |- all_bound ?comps ==> bound ?c * all_bound_drop ?comps ?c ] =>
    apply unpack_all_bound
  | [ |- bound ?c * all_bound_drop ?comps ?c ==> all_bound ?comps ] =>
    apply repack_all_bound
  | [ |- bound ?c * all_bound_drop ?comps ?c ==> all_bound ?comps * _ ] =>
    apply himp_comm_conc; apply himp_prop_conc
  | [ |- all_bound_drop ?comps ?c * bound ?c ==> all_bound ?comps ] =>
    apply himp_comm_prem
  | [ _: KTrace ?x |- KTrace (_ ++ ?x) ] => econstructor; [eauto|]
  | [ _: KTrace ?x |- KTrace ?t ] =>
    match t with context [x] => repeat (rewrite app_assoc) end
  | [ |- AddedValidExchange _ _ ] => constructor
  | [ |- ValidExchange ((_ ++ _) ++ _) ] => repeat (rewrite <- app_assoc)
  | [ |- ValidExchange _ ] => constructor
  end.

Ltac simplr := try simplr_fail; auto.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    %s
  );
  sep unfoldr simplr.
Qed.

Definition exchange :
  forall (%s : chan) (kst : kstate),
  STsep (kstate_inv kst * [In c (components kst)])
        (fun (kst' : kstate) => kstate_inv kst').
Proof.
  intros ? [comps tr]; refine (
    req <- recv_msg c tr <@> [In c comps] * all_bound_drop comps c * (tr ~~
    [KTrace tr]);
    match req with
%s
      (* special case for errors *)
      | BadTag tag =>
        {{ Return (mkst comps (tr ~~~ RecvMsg c (BadTag tag) ++ tr)) }}
    end
  );
  sep unfoldr simplr.
Qed.
"

let coq_of_kernel s =
  let m = gen_tag_map s in
  let fmt l f =
    String.concat "\n" (List.map f l)
  in
  let xch_chan, handlers = s.exchange in
  mkstr coq_template
    (fmt s.constants coq_of_constant_decl)
    (fmt s.msg_decls coq_of_msg_decl)
    (fmt s.msg_decls (coq_trace_recv_msg m))
    (fmt s.msg_decls (coq_trace_send_msg m))
    (fmt s.msg_decls (coq_recv_msg m))
    (fmt s.msg_decls (coq_send_msg m))
    (fmt handlers (coq_spec_of_handler xch_chan))
    (
      let t = coq_trace_of_prog [] s.init in
      let v = prog_vars s.init in
      match v with
      | [] -> mkstr "KTrace (%snil)" t
      | _  ->
        mkstr "forall %s, KTrace (%snil)"
          (String.concat " " v) t
    )
    (coq_of_init s.init) (* kinit *)
    xch_chan
    (fmt handlers (coq_of_handler xch_chan))
