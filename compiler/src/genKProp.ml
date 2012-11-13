open Common
open Kernel
open Gen

let coq_of_param_typ = function
  | Num   -> "Num"
  | Str   -> "Str"
  | Chan  -> "Chan"
  | Fdesc -> "Fdesc"

let msgpat_case m =
  m.payload
    |> List.map coq_of_param_typ
    |> List.map (mkstr "ParamPat %s -> ")
    |> String.concat ""
    |> mkstr "| MP_%s : %sMsgPat" m.tag

let msgmatch_case m =
  let hyps =
    m.payload
      |> mapi (fun i t ->
          mkstr "  forall pp%d p%d, ParamMatch %s ctx pp%d p%d ->"
            i i (coq_of_param_typ t) i i)
      |> String.concat "\n"
      |> function "" -> "" | s -> "\n" ^ s
  in
  let pps =
    m.payload
      |> mapi (fun i _ -> mkstr " pp%d" i)
      |> String.concat ""
  in
  let ps =
    m.payload
      |> mapi (fun i _ -> mkstr " p%d" i)
      |> String.concat ""
  in
  mkstr "\
| MM_%s :
  ctx = ctx ->%s
  MsgMatch (MP_%s%s) (%s%s)"
    m.tag hyps m.tag pps m.tag ps

let cpp = function
  | PP_Any t      -> mkstr "PP_Any %s" (coq_of_param_typ t)
  | PP_Lit (t, v) -> mkstr "PP_Lit %s (%s)" (coq_of_param_typ t) v
  | PP_Var (t, n) -> mkstr "PP_Var %s %d" (coq_of_param_typ t) n

let ckmp (tag, params) =
  match params with
  | [] ->
      mkstr "MP_%s" tag
  | _ ->
      params
        |> List.map cpp
        |> String.concat ") ("
        |> mkstr "MP_%s (%s)" tag

let ckap = function
  | KAP_Any            -> "KAP_Any"
  | KAP_KSend (cp, mp) -> mkstr "KAP_KSend (%s) (%s)" (cpp cp) (ckmp mp)
  | KAP_KRecv (cp, mp) -> mkstr "KAP_KRecv (%s) (%s)" (cpp cp) (ckmp mp)

let rec cktp = function
  | KTP_Emp    -> "KTP_Emp"
  | KTP_Act  x -> mkstr "KTP_Act (%s)"  (ckap x)
  | KTP_NAct x -> mkstr "KTP_NAct (%s)" (ckap x)
  | KTP_Star a -> mkstr "KTP_Star (%s)" (cktp a)
  | KTP_Alt (a, b) -> mkstr "KTP_Alt (%s) (%s)" (cktp a) (cktp b)
  | KTP_And (a, b) -> mkstr "KTP_And (%s) (%s)" (cktp a) (cktp b)
  | KTP_Cat (a, b) -> mkstr "KTP_Cat (%s) (%s)" (cktp a) (cktp b)
  | KTP_Ctx_ChanT (var, chanT) -> mkstr "KTP_Ctx_ChanT %d %s" var chanT

let coq_of_kt_spec = function
  | KTS_Pat  p -> mkstr "KTS_Pat  (%s)" (cktp p)
  | KTS_NPat p -> mkstr "KTS_NPat (%s)" (cktp p)

(* pretty print regexps *)

let pretty_pp = function
  | PP_Any _      -> "_"
  | PP_Lit (_, v) -> "\"" ^ v ^ "\""
  | PP_Var (_, v) -> string_of_int v

let pretty_mp (tag, params) =
  params
    |> List.map pretty_pp
    |> String.concat ", "
    |> mkstr "%s(%s)" tag

let pretty_kap = function
  | KAP_Any            -> "_"
  | KAP_KSend (cp, mp) -> mkstr "send(%s, %s)" (pretty_pp cp) (pretty_mp mp)
  | KAP_KRecv (cp, mp) -> mkstr "recv(%s, %s)" (pretty_pp cp) (pretty_mp mp)

let rec pretty_tp = function
  | KTP_Emp    -> "0"
  | KTP_Act  x -> mkstr "[%s]"  (pretty_kap x)
  | KTP_NAct x -> mkstr "[^%s]" (pretty_kap x)
  | KTP_Star a -> mkstr "(%s)* " (pretty_tp a)
  | KTP_Alt (a, b) -> mkstr "(%s | %s)" (pretty_tp a) (pretty_tp b)
  | KTP_And (a, b) -> mkstr "(%s & %s)" (pretty_tp a) (pretty_tp b)
  | KTP_Cat (a, b) -> mkstr "%s %s"      (pretty_tp a) (pretty_tp b)
  | KTP_Ctx_ChanT (var, chanT) -> mkstr "<<%d HASCHANTYPE %s>>" var chanT

let pretty_kt_spec = function
  | KTS_Pat  p -> mkstr "ALWAYS_MATCH : %s"  (pretty_tp p)
  | KTS_NPat p -> mkstr "NEVER_MATCH : %s" (pretty_tp p)

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
    (* %s *)
    (%s)
    tr.
Proof.
  ktm.
Qed.
" name (pretty_kt_spec p) (coq_of_kt_spec p)

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
