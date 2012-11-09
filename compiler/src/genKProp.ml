open Common
open Kernel
open Gen

let msgpat_case m =
  mkstr "| MP_%s : MsgVar -> %s MsgPat" m.tag (fmt m.payload (fun _ -> "MsgVar -> "))

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

let cmsgvar varname = if varname == "_" then "MV_Any" else (mkstr "MV_Name %s" varname)
let cmsgvars varnames = fmt varnames (fun v -> cmsgvar v)

let ckap = function
  | KAP_Any     -> "KAP_Any"
  | KAP_KSend (c,msg_tag,vars) -> mkstr "KAP_KSend %s MP_%s %s" c msg_tag (cmsgvars vars)
  | KAP_KRecv (c,msg_tag,vars) -> mkstr "KAP_KRecv %s MP_%s %s" c msg_tag (cmsgvars vars)

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

let fold_kstate_field (id, _) =
  mkstr "  fold (Kernel.%s s) in *;" id

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
  ktmatch.
Qed.
" name (coq_of_kt_spec p)

let subs k =
  List.map (fun (f, r) ->
    (Str.regexp ("(\\* *__" ^ f ^ "__ *\\*)"), r))
  [ "MSGPAT_CASES",
      fmt k.msg_decls msgpat_case
  ; "MSGMATCH_CASES",
      fmt k.msg_decls msgmatch_case
  ; "FOLD_KSTATE_TAC",
      fmt k.var_decls fold_kstate_field
  ; "PROPERTIES",
      fmt k.props coq_of_prop
  ]
