open Common
open Kernel

let lines l = String.concat "\n" (List.filter (fun s -> s <> "") l)

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

let coq_of_kernel s =
  let fmt l f = lines (List.map f l) in
  let (add, contents) = mk_buffer () in
  add "
Require Import Ascii.
Require Import List.
Require Import String.
Require Import Ynot.
Require Import KrakenLib.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.
";
  add (fmt s.constants coq_of_constant_decl);
  add "
Inductive chan_type : Set :=
";
  add (fmt s.components (fun (id, _) -> "| " ^ id));
  add ".

Definition chan_path (t: chan_type): str :=
  match t with
";
  add (fmt s.components
        (fun (id, path) ->
          mkstr "  | %s => string2str \"%s\"" id path)
  );
  (* TODO?: Move a big chunk of what's next in a template file.
    If so, remember to unescape "001"
   *)
  add "
  end.

Axiom chan : chan_type -> Set.

Definition tchan := sigT (fun t : chan_type => chan t).

Axiom tchan_eq : forall (c1 c2 : tchan), { c1 = c2 } + { c1 <> c2 }.

Lemma tchan_eq_true :
  forall (c : tchan) (A : Type) (vT vF : A),
  (if tchan_eq c c then vT else vF) = vT.
Proof.
  intros; case (tchan_eq c c); auto. congruence.
Qed.

Lemma tchan_eq_false :
  forall (c1 c2 : tchan) (A : Type) (vT vF : A),
  c1 <> c2 ->
  (if tchan_eq c1 c2 then vT else vF) = vF.
Proof.
  intros; case (tchan_eq c1 c2); auto. congruence.
Qed.

Axiom fdesc : Set.

Inductive Action : Set :=
| Exec   : str -> tchan -> Action
| Call   : str -> str -> fdesc -> Action
| Select : list tchan -> tchan -> Action
| Recv   : tchan -> str -> Action
| Send   : tchan -> str -> Action
| RecvFD : tchan -> fdesc -> Action
| SendFD : tchan -> fdesc -> Action.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Axiom bound : tchan -> hprop.

Axiom exec :
  forall (t: chan_type) (prog : str) (tr : [Trace]),
    STsep (tr ~~ traced tr * [prog = chan_path t])
    (fun (c: tchan) =>
      tr ~~ bound c * traced (Exec prog c :: tr) * [projT1 c = t]).

Axiom call :
  forall (prog arg : str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (f : fdesc) => tr ~~ traced (Call prog arg f :: tr)).

(* TODO add non-empty precondition *)
Axiom select :
  forall (chans : list tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (c : tchan) => tr ~~ traced (Select chans c :: tr) * [In c chans]).

Axiom recv :
  forall (c : tchan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (Recv c s :: tr) * bound c *
          [nat_of_num n = List.length s]).

Axiom send :
  forall (c : tchan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (Send c s :: tr) * bound c).

Axiom recv_fd :
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (f : fdesc) => tr ~~ traced (RecvFD c f :: tr) * bound c).

Axiom send_fd :
  forall (c : tchan) (f : fdesc) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendFD c f :: tr) * bound c).

Definition RecvNum (c : tchan) (n : num) : Trace :=
  match n with
  | Num a1 => Recv c (a1 :: nil) :: nil
  end.

Definition recv_num:
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (n : num) => tr ~~ traced (RecvNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    s <- recv c (Num \"001\") tr;
    match s with
    | a1 :: nil =>
      {{ Return (Num a1) }}
    | _ => (* bogus *)
      {{ Return (Num zero) }}
    end
  );
  sep fail auto.
  compute in H; discriminate.
  compute in H; discriminate.
Qed.

Definition SendNum (c : tchan) (n : num) : Trace :=
  match n with
  | Num a1 => Send c (a1 :: nil) :: nil
  end.

Definition send_num:
  forall (c : tchan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    match n with
    | Num a1 =>
      send c (a1 :: nil) tr;;
      {{ Return tt }}
    end
  );
  sep fail auto.
Qed.

Definition RecvStr (c : tchan) (s : str) : Trace :=
  Recv c s :: RecvNum c (num_of_nat (List.length s)).

Definition recv_str:
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (RecvStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recv_num c tr;
    s <- recv c n (tr ~~~ RecvNum c n ++ tr);
    {{ Return s }}
  );
  sep fail auto.
  rewrite <- H.
  rewrite num_nat_embedding.
  sep fail auto.
Qed.

Definition SendStr (c : tchan) (s : str) : Trace :=
  Send c s :: SendNum c (num_of_nat (List.length s)).

Definition send_str:
  forall (c : tchan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    let n := num_of_nat (List.length s) in
    send_num c n tr;;
    send c s (tr ~~~ SendNum c n ++ tr);;
    {{ Return tt }}
  );
  sep fail auto.
Qed.

(* trace versions of basic actions so we can always use app (++) *)

Definition Exec_t (prog : str) (c : tchan) : Trace :=
  Exec prog c :: nil.

Definition Call_t (prog arg : str) (f : fdesc) : Trace :=
  Call prog arg f :: nil.

Definition RecvFD_t (c : tchan) (f : fdesc) : Trace :=
  RecvFD c f :: nil.

Definition SendFD_t (c : tchan) (f : fdesc) : Trace :=
  SendFD c f :: nil.

(* prevent sep tactic from unfolding *)
Global Opaque RecvStr SendStr Exec_t Call_t RecvFD_t SendFD_t.

Inductive msg : Set :=
";
  add (fmt s.msg_decls coq_of_msg_decl);
  add "
(* special case for errors *)
| BadTag : num -> msg.

Definition RecvMsg (c : tchan) (m : msg) : Trace :=
  match m with
";
  let m = gen_tag_map s in
  add (fmt s.msg_decls (coq_trace_recv_msg m));
  add "
  (* special case for errors *)
  | BadTag p0 =>
    RecvNum c p0
  end.

Definition SendMsg (c : tchan) (m : msg) : Trace :=
  match m with
";
  add (fmt s.msg_decls (coq_trace_send_msg m));
  add "
  (* special case for errors *)
  | BadTag p0 =>
    SendNum c (Num \"000\")
  end.

Definition recv_msg :
  forall (c : tchan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (m : msg) => tr ~~ traced (RecvMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    tag <- recv_num c tr;
    match tag with
";
  add (fmt s.msg_decls (coq_recv_msg m));
  add "
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
  forall (c : tchan) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendMsg c m ++ tr) * bound c).
Proof.
  intros; refine (
    match m with
";
  add (fmt s.msg_decls (coq_send_msg m));
  add "
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

Inductive ValidExchange : Trace -> Prop :=";
  add (
    let (xch_chan, exchanges) = s.exchange in
    fmt exchanges
      (fun (comp, handlers) ->
        fmt handlers (coq_spec_of_handler s comp xch_chan)
      )
  );
  (* for now, add a case for each cross-product that is not handled *)
  add (
    let (xch_chan, exchanges) = s.exchange in
    fmt exchanges (fun (comp, handlers) ->
      let rest = List.filter
        (fun m ->
          not (List.exists (fun h -> h.trigger.tag = m.tag) handlers)
        )
        s.msg_decls
      in
      fmt rest (fun m ->
        let args = m.payload |> List.map coq_of_typ |> String.concat " " in
        Printf.sprintf "
| VE_%s_%s:
  forall %s %s, ValidExchange (RecvMsg %s (%s %s))"
          comp m.tag args xch_chan xch_chan m.tag args
      )
    )
  );
  add "
(* special case for errors *)
| VE_BadTag :
  forall c tag,
  ValidExchange (
    RecvMsg c (BadTag tag)).

Hint Constructors ValidExchange.

Inductive AddedValidExchange : Trace -> Trace -> Prop :=
| AVE_intro :
  forall tr1 tr2,
  ValidExchange tr2 ->
  AddedValidExchange tr1 (tr2 ++ tr1).

Hint Constructors AddedValidExchange.

Inductive KTrace : Trace -> Prop :=
| KT_init :
";
  add (
    let t = coq_trace_of_prog s [] s.init in
    let v = prog_vars s.init in
    match v with
    | [] -> mkstr "KTrace (%snil)" t
    | _  -> mkstr "forall %s, KTrace (%snil)" (String.concat " " v) t
  );
  add "
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

Fixpoint all_bound (cs : list tchan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' => bound c * all_bound cs'
  end.

(* all cs bound except _first_ occurrence of drop *)
Fixpoint all_bound_drop (cs : list tchan) (drop : tchan) : hprop :=
  match cs with
    | nil => emp
    | c :: cs' =>
      if tchan_eq c drop then
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
  destruct H; subst. rewrite tchan_eq_true. apply himp_refl.
  case (tchan_eq a c); intros; subst. apply himp_refl.
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
  destruct H; subst. rewrite tchan_eq_true. apply himp_refl.
  case (tchan_eq a c); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.

Record kstate : Set :=
  mkst { components : list tchan
       ; ktr : [Trace]
";
  add (
    match s.var_decls with
    | [] -> ""
    | l -> fmt l (fun (id, typ) -> mkstr "; %s : %s" id (coq_of_typ typ))
  );
  add "
       }.

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
";
  add (coq_of_init s);
  add "
  );
  sep unfoldr simplr.
Qed.

";
  let kern_state_vars = s.var_decls |> List.map fst |> String.concat " " in
  let (xch_chan, exchanges) = s.exchange in
  add (fmt exchanges (fun (comp, handlers) ->
    (* c should be %s xch_chan, but there's plenty of them :( *)
    Printf.sprintf "
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
      comp
      kern_state_vars
      (fmt handlers (coq_of_handler s xch_chan))
      kern_state_vars
      (
        match
          List.filter
            (fun msg -> not (
              List.exists
                (fun h -> h.trigger.tag = msg.tag)
                handlers
            ))
            s.msg_decls
        with
        | [] -> ""
        | _ ->
          Printf.sprintf
"    (* non-handled cases *)
    | msg =>
      {{ Return (mkst comps (tr ~~~ RecvMsg c msg ++ tr) %s) }}
"
            kern_state_vars
      )
  ));
  add "
Fixpoint type_of_comp
  (c: tchan) (comps: list tchan): chan_type :=
  match comps with";
  add (Printf.sprintf "
  | nil => %s (* TODO: need default or proof *)"
    (fst (List.hd s.components))
  );
  add "
  | x :: rest =>
    if tchan_eq x c
      then projT1 x
      else type_of_comp c rest
  end.

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.";
  add (Printf.sprintf "
  intros [comps tr %s];" kern_state_vars);
  add "
  refine (
    comp <- select comps tr
    <@> (tr ~~ [KTrace tr] * all_bound comps);
    let handler := (
      match type_of_comp comp comps with";
  add (
    String.concat "" (List.map (fun (comp, _) -> Printf.sprintf "
      | %s => exchange_%s" comp comp
    ) s.components)
  );
  add "
      end
    ) in";
  add (Printf.sprintf "
    s' <- handler comp (mkst comps (tr ~~~ Select comps comp :: tr) %s);"
    kern_state_vars
  );
  add "
    {{ Return s' }}
  );
  sep unfoldr simplr.
Qed.
";
  contents ()

(*

*)
