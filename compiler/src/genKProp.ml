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

let ckap = function
  | KAP_Any     -> "KAP_Any"
  | KAP_KSend s -> mkstr "KAP_KSend MP_%s" s
  | KAP_KRecv s -> mkstr "KAP_KRecv MP_%s" s

let rec cktp = function
  | KTP_Emp    -> "KTP_Emp"
  | KTP_Act  x -> mkstr "KTP_Act (%s)"  (ckap x)
  | KTP_NAct x -> mkstr "KTP_NAct (%s)" (ckap x)
  | KTP_Star a -> mkstr "KTP_Star (%s)" (cktp a)
  | KTP_Alt (a, b) -> mkstr "KTP_Alt (%s) (%s)" (cktp a) (cktp b)
  | KTP_And (a, b) -> mkstr "KTP_And (%s) (%s)" (cktp a) (cktp b)
  | KTP_Cat (a, b) -> mkstr "KTP_Cat (%s) (%s)" (cktp a) (cktp b)

let coq_of_kt_spec = function
  | KTS_Pat  p -> mkstr "KTS_Pat  (%s)" (cktp p)
  | KTS_NPat p -> mkstr "KTS_NPat (%s)" (cktp p)

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
  | KTracePat p ->
      mkstr "
Theorem %s :
  forall kst, KInvariant kst ->
  forall tr, ktr kst = [tr]%%inhabited ->
  KTraceMatchSpec
    (%s)
    tr.
Proof.
  induction 1; [ | |
    match goal with
    | H: ValidExchange _ _ |- _ => inv H
    end
  ]; simpl; intros; uninhabit; ktm.
Qed.
" name (coq_of_kt_spec p)

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
