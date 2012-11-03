open Common
open Kernel
open Gen

let msgpat_case m =
  mkstr "| MP_%s" m.tag

let msgmatch_case m =
  match m.payload with
  | [] ->
      mkstr "
| MM_%s :
    MsgMatch MP_%s %s"
      m.tag m.tag m.tag
  | _ ->
      let args = coq_of_args m in
      mkstr "
| MM_%s :
  forall %s,
  MsgMatch MP_%s (%s %s)"
        m.tag args m.tag m.tag args

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
  unfold ImmAfter; induction 2; simpl; intros; imm_tac.
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
  unfold ImmBefore; induction 2; simpl; intros; imm_tac.
Qed.
" name bef aft

let subs s =
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "MSGPAT_CASES",
      fmt s.msg_decls msgpat_case
  ; "MSGMATCH_CASES",
      fmt s.msg_decls msgmatch_case
  ; "PROPERTIES",
      fmt s.props coq_of_prop
  ]
