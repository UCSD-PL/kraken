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

let coq_of_ka_pat = function
  | KAP_KSend s -> mkstr "KAP_KSend MP_%s" s
  | KAP_KRecv s -> mkstr "KAP_KRecv MP_%s" s

let coq_of_ka_pats kaps =
  kaps
    |> List.map coq_of_ka_pat
    |> List.map (mkstr "%s :: ")
    |> String.concat ""
    |> mkstr "(%snil)"

let rec coq_of_kt_pat = function
  | KTP_Empty ->
      "KTP_Empty"
  | KTP_Class kaps ->
      mkstr "KTP_Class %s" (coq_of_ka_pats kaps)
  | KTP_NegClass kaps ->
      mkstr "KTP_NegClass %s" (coq_of_ka_pats kaps)
  | KTP_Cat (p1, p2) ->
      mkstr "KTP_Cat (%s) (%s)"
        (coq_of_kt_pat p1)
        (coq_of_kt_pat p2)
  | KTP_Alt (p1, p2) ->
      mkstr "KTP_Alt (%s) (%s)"
        (coq_of_kt_pat p1)
        (coq_of_kt_pat p2)
  | KTP_Star p ->
      mkstr "KTP_Star (%s)"
        (coq_of_kt_pat p)

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
  KTraceMatch
    (%s)
    tr.
Proof.
  induction 1; [ | |
    match goal with
    | H: ValidExchange _ _ |- _ => inv H
    end
  ]; simpl; intros; uninhabit; ktm.
Qed.
" name (coq_of_kt_pat p)

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
