Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import ActionMatch.
Require Import PolLang.
Require Import Ynot.

Section PolLangFacts.

Context {NB_MSG : nat}.
Variable PAYD     : vvdesc NB_MSG.
Variable COMPT    : Set.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Variable COMPS    : COMPT -> compd.
Variable IENVD    : vcdesc COMPT.
Variable KSTD     : vcdesc COMPT.
Variable HANDLERS : handlers PAYD COMPT COMPS KSTD.

Fixpoint no_match {envd term} (c:cmd PAYD COMPT COMPS KSTD term envd)
         (oact:KOAction PAYD COMPT COMPS) :=
  match c with
  | Reflex.Seq _ c1 c2 =>
    no_match c1 oact /\
    no_match c2 oact
  | Reflex.Ite _ _ c1 c2 =>
    no_match c1 oact /\
    no_match c2 oact
  | Reflex.Send _ ct _ t _ =>
    match oact with
    | KOSend (Some (Build_conc_pat ct' _)) (Some (Build_opt_msg t' _)) =>
      if COMPTDEC ct ct'
      then if fin_eq_dec t t'
           then False
           else True
      else True
    | KOSend None (Some (Build_opt_msg t' _)) =>
      if fin_eq_dec t t'
      then False
      else True
    | KOSend (Some (Build_conc_pat ct' _)) None =>
      if COMPTDEC ct ct'
      then False
      else True
    | KOSend None None => False
    | _ => True
    end
  | Reflex.Spawn _ ct _ _ _ =>
    match oact with
    | KOExec _ _ (Some (Build_conc_pat ct' _)) =>
      if COMPTDEC ct ct'
      then False
      else True
    | KOExec _ _ None => False
    | _ => True
    end
  | Reflex.Call _ _ _ _ _ =>
    match oact with
    | KOCall _ _ _ => False
    | _ => True
    end
  | Reflex.InvokeFD _ _ _ _ _ =>
    match oact with
    | KOInvokeFD _ _ _ => False
    | _ => True
    end
  | Reflex.InvokeStr _ _ _ _ _ =>
    match oact with
    | KOInvokeStr _ _ _ => False
    | _ => True
    end
  | Reflex.StUpd _ _ _ => True
  | Reflex.CompLkup _ _ c1 c2 =>
    no_match c1 oact /\
    no_match c2 oact
  | Reflex.Nop _ => True
  end.

Lemma no_match_initial_init_state : forall oact,
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
  init_ktr _ _ _ _ _ (initial_init_state _ _ _ KSTD IENVD)  = inhabits tr ->
  forall act, List.In act tr ->
               ~ActionMatch.AMatch PAYD COMPT COMPS COMPTDEC oact act.
Proof.
  intros oact tr Htr.
  simpl in Htr; apply pack_injective in Htr;
  subst tr. auto.
Qed.

Lemma no_match_init : forall init input oact s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) oact ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   forall act, List.In act tr ->
               ~ActionMatch.AMatch PAYD COMPT COMPS COMPTDEC oact act.
Proof.
  intros init input oact s Hinit Hno_en tr Htr act Hin.
  inversion Hinit. clear Hinit.
  subst s0. subst s. simpl in *.
  generalize dependent tr. generalize dependent act.
  pose proof (no_match_initial_init_state oact).
  generalize dependent (initial_init_state PAYD COMPT COMPS KSTD IENVD).
  destruct init as [init pf]. simpl in *. clear pf.
  induction init; simpl in *; intros; eauto.
    destruct input as [input1 input2]. simpl in *.
    destruct Hno_en as [Hno_en1 Hno_en2].
    specialize (IHinit1 input1 Hno_en1 i H).
    eapply (IHinit2 input2 Hno_en2
           (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd i init1
                input1)); eauto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ if ?e then _ else _ ] |- _ ]
        => destruct e
    end.
      eapply IHinit2; eauto.
      eapply IHinit1; eauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i).
    simpl in *. apply pack_injective in Htr.
    subst tr. simpl in *. decompose [or] Hin; eauto.
      subst act. destruct oact; auto.
      destruct o; destruct o0; auto.
      destruct c; destruct o; simpl in *.
      unfold msgMatch', match_comp'.
      destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
      simpl. destruct x. subst ct. simpl in *.
      destruct (COMPTDEC comp_type conc_pat_type); try tauto.
      destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
      simpl. unfold match_comp'.
      destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
      simpl. destruct x. subst ct. simpl in *.
      destruct c; destruct (COMPTDEC comp_type conc_pat_type);
      try contradiction; tauto.
      destruct o. simpl. unfold msgMatch'. simpl.
      destruct (fin_eq_dec t opt_tag); try contradiction; tauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. simpl in *. decompose [or] Hin; eauto.
    subst act. destruct oact; auto. destruct o1; try contradiction.
    destruct c. simpl.
    destruct (COMPTDEC t conc_pat_type); try tauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. simpl in *. decompose [or] Hin; eauto.
    subst act. destruct oact; auto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. simpl in *. decompose [or] Hin; eauto.
    subst act. destruct oact; auto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. simpl in *. decompose [or] Hin; eauto.
    subst act. destruct oact; auto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
        => destruct e
    end.
    simpl in *.
      eapply IHinit1; eauto; simpl; auto.
      eapply IHinit2; eauto.
Qed.

Lemma list_app_cons : forall (A:Type) x (l:List.list A),
  x :: l = (x::nil) ++ l.
Proof.
  auto.
Qed.

Lemma no_match_hdlr' : forall c m oact (P:Reflex.KTrace _ _ _ -> Prop),
  let hdlrs := HANDLERS (tag _ m) (comp_type _ _ c) in
  forall s s' input,
  hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m
    (projT1 hdlrs) s (proj1_sig (projT2 hdlrs)) input = s' ->
  no_match (proj1_sig (projT2 hdlrs)) oact ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s) = inhabits tr ->
   P tr) ->
  (forall tr tr',
     P tr ->
     (forall a, List.In a tr' -> ~ActionMatch.AMatch PAYD COMPT COMPS COMPTDEC oact a) ->
     P (tr' ++ tr)) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s') = inhabits tr ->
   P tr.
Proof.
  intros c m oact P hdlrs s s' input Hrun Hno Hind Hp tr Htr.
  destruct hdlrs as [envd cmd]. simpl in *. subst s'.
  generalize dependent tr.
  destruct cmd as [cmd ?]. simpl in *. clear h.
  induction cmd; simpl in *; intros; auto.
    destruct input as [input1 input2]. simpl in *.
    destruct Hno as [Hno_en1 Hno_en2].
    specialize (IHcmd1 s input1 Hno_en1 Hind).
    eapply IHcmd2; eauto.

    destruct Hno as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ if ?e then _ else _ ] |- _ ]
        => destruct e
    end.
      eapply IHcmd2; eauto.
      eapply IHcmd1; eauto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. rewrite list_app_cons.
    apply Hp; auto. intros a Ha. simpl in *.
    decompose [or] Ha; auto.
    subst a. destruct oact; auto.
    destruct o; destruct o0; auto.
    destruct o; simpl in *.
    unfold msgMatch', match_comp'.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
              (kst PAYD COMPT COMPS KSTD s) env e).
    simpl. destruct x. subst ct. simpl in *. destruct c0.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    simpl. unfold match_comp'.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
              (kst PAYD COMPT COMPS KSTD s) env e).
    simpl. destruct x. subst ct. simpl in *.
    destruct c0; destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; tauto.
    destruct o. simpl. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. rewrite list_app_cons.
    apply Hp; auto. intros a Ha. simpl in *.
    decompose [or] Ha; auto.
    subst a. destruct oact; auto.
    destruct o1; try contradiction.
    destruct c0. simpl.
    destruct (COMPTDEC t conc_pat_type); try tauto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. rewrite list_app_cons.
    apply Hp; auto. intros a Ha. simpl in *.
    decompose [or] Ha; auto.
    subst a. destruct oact; auto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. rewrite list_app_cons.
    apply Hp; auto. intros a Ha. simpl in *.
    decompose [or] Ha; auto.
    subst a. destruct oact; auto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. rewrite list_app_cons.
    apply Hp; auto. intros a Ha. simpl in *.
    decompose [or] Ha; auto.
    subst a. destruct oact; auto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. auto.

    destruct Hno as [Hno_en1 Hno_en2].
    destruct s as [s env].
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
        => destruct e
    end.
    simpl in *.
      eapply IHcmd1; eauto; simpl; auto.
      eapply IHcmd2; eauto.
Qed.

Definition not_recv_match ct t (oact:KOAction PAYD COMPT COMPS) :=
  match oact with
  | KORecv (Some (Build_conc_pat ct' _)) (Some (Build_opt_msg t' _)) =>
    if COMPTDEC ct ct'
    then if fin_eq_dec t t'
         then False
         else True
    else True
  | KORecv None (Some (Build_opt_msg t' _)) =>
    if fin_eq_dec t t'
    then False
    else True
  | KORecv (Some (Build_conc_pat ct' _)) None =>
    if COMPTDEC ct ct'
    then False
    else True
  | KORecv None None => False
  | _ => True
  end.

Definition not_select_match ct (oact:KOAction PAYD COMPT COMPS) :=
  match oact with
  | KOSelect _ (Some (Build_conc_pat ct' _)) =>
    if COMPTDEC ct ct'
    then False
    else True
  | KOSelect _ None => False
  | _ => True
  end.
  
Lemma no_match_hdlr : forall c m input oact s s' (P : Reflex.KTrace _ _ _ -> Prop),
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) oact ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact ->
  not_select_match (comp_type _ _ c) oact ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   P tr) ->
  (forall tr tr',
     P tr ->
     (forall a, List.In a tr' -> ~ActionMatch.AMatch PAYD COMPT COMPS COMPTDEC oact a) ->
     P (tr' ++ tr)) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   P tr.
Proof.
  intros c m input oact s s' P Hve Hno_match
         Hno_recv Hno_select Hind Hp tr Htr.
  inversion Hve. unfold kstate_run_prog in *.
  clear Hve. subst s'0. subst s'. clear H2 H.
  eapply no_match_hdlr'; eauto.
  clear dependent tr. simpl. intros tr Htr.
  apply pack_injective in Htr; subst tr.
  rewrite list_app_cons with (l:=tr0).
  rewrite List.app_comm_cons.
  apply Hp; auto. intros a Ha. simpl in *.
  decompose [or] Ha; auto; subst a.
    destruct oact; auto. simpl in *.
    destruct o; destruct o0; try contradiction.
    destruct c0. simpl. unfold match_comp'.
    destruct c. simpl in *.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct o. unfold msgMatch'. simpl.
    destruct (fin_eq_dec (tag _ m) opt_tag); try contradiction; tauto.
    destruct c0. simpl. unfold match_comp'.
    destruct c. simpl in *.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct o. simpl. unfold msgMatch'. simpl.
    destruct (fin_eq_dec (tag _ m) opt_tag); try contradiction; tauto.

    destruct oact; auto. simpl in *.
    destruct o; destruct o0; try contradiction;
    destruct c0; simpl; destruct c; simpl in *;
    destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; try tauto.
Qed.

Lemma enables_no_match : forall oact oact' tr tr',
  Enables PAYD COMPT COMPS COMPTDEC oact oact' tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC oact' a) ->
  Enables _ _ _ COMPTDEC oact oact' (tr' ++ tr).
Proof.
  intros oact oact' tr tr' Hen Hno_match.
  induction tr'.
    auto.

    apply E_not_future. apply IHtr'.
      intros a0 Hina0.
      apply Hno_match. simpl. auto.

      apply Hno_match. simpl. auto.
Qed.

Lemma no_enablee_init : forall init input oact oact' s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) oact' ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros. rewrite <- List.app_nil_r.
  apply enables_no_match.
    constructor.

    eapply no_match_init; eauto.
Qed.

Lemma no_enablee_hdlr : forall c m input oact oact' s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) oact' ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact' ->
  not_select_match (comp_type _ _ c) oact' ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros.
  eapply no_match_hdlr; eauto.
  apply enables_no_match.
Qed.

Lemma enables_compose : forall A B T1 T2,
  Enables PAYD COMPT COMPS COMPTDEC A B T1 ->
  Enables _ _ _ COMPTDEC A B T2 ->
  Enables _ _ _ COMPTDEC A B (T2 ++ T1).
Proof.
  intros A B T1 T2 Hen1 Hen2.
  induction Hen2.
    simpl. auto.

    simpl. apply E_not_future; auto.

    simpl. apply E_future; auto.
    destruct H as [a H].
    exists a. intuition.
Qed.

Lemma ensures_no_match : forall A B tr tr',
  Ensures PAYD COMPT COMPS COMPTDEC A B tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC A a) ->
  Ensures _ _ _ COMPTDEC A B (tr' ++ tr).
Proof.
  unfold Ensures.
  intros A B tr tr' Hen Hno_match.
  rewrite List.rev_app_distr.
  apply enables_compose; auto.
  induction tr'.
    constructor.

    simpl. apply enables_compose.
      apply E_not_future.
        constructor.

        apply Hno_match; simpl; auto.

      apply IHtr'. intros a0 Hin0.
      apply Hno_match; simpl; auto.
Qed.

Lemma no_ensurer_init : forall init input A B s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) A ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Ensures PAYD COMPT COMPS COMPTDEC A B tr.
Proof.
  intros. rewrite <- List.app_nil_r.
  apply ensures_no_match.
    constructor.

    eapply no_match_init; eauto.
Qed.

Lemma no_ensurer_hdlr : forall c m input A B s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) A ->
  not_recv_match (comp_type _ _ c) (tag _ m) A ->
  not_select_match (comp_type _ _ c) A ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Ensures PAYD COMPT COMPS COMPTDEC A B tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   Ensures PAYD COMPT COMPS COMPTDEC A B tr.
Proof.
  intros.
  eapply no_match_hdlr; eauto.
  apply ensures_no_match.
Qed.

Lemma immbefore_no_match : forall oact oact' tr tr',
  ImmBefore PAYD COMPT COMPS COMPTDEC oact oact' tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC oact' a) ->
  ImmBefore _ _ _ COMPTDEC oact oact' (tr' ++ tr).
Proof.
  intros oact oact' tr tr' Hen Hno_match.
  induction tr'.
    auto.

    apply IB_nB. apply IHtr'.
      intros a0 Hina0.
      apply Hno_match. simpl. auto.

      apply Hno_match. simpl. auto.
Qed.

Lemma no_after_IB_init : forall init input oact oact' s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) oact' ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   ImmBefore PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros. rewrite <- List.app_nil_r.
  apply immbefore_no_match.
    constructor.

    eapply no_match_init; eauto.
Qed.

Lemma no_after_IB_hdlr : forall c m input oact oact' s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) oact' ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact' ->
  not_select_match (comp_type _ _ c) oact' ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   ImmBefore PAYD COMPT COMPS COMPTDEC oact oact' tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   ImmBefore PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros.
  eapply no_match_hdlr; eauto.
  apply immbefore_no_match.
Qed.

Lemma IB_compose : forall A B T1 T2,
  ImmBefore PAYD COMPT COMPS COMPTDEC A B T1 ->
  ImmBefore PAYD COMPT COMPS COMPTDEC A B T2 ->
  ImmBefore PAYD COMPT COMPS COMPTDEC A B (T2 ++ T1).
Proof.
  intros A B T1 T2 H1 H2.
  induction H2.
    simpl. auto.

    simpl. apply IB_nB; auto.

    simpl in *. apply IB_A; auto.
Qed.

(*Inductive ImmAfterStrong B A :
  KTrace PAYD COMPT COMPS -> Prop :=
| IAS_nil : ImmAfterStrong B A nil
| IAS_cons : forall a tr,
               ImmAfter _ _ _ COMPTDEC B A (a::tr) ->
               ~ActionMatch.AMatch _ _ _ COMPTDEC A a ->
               ImmAfterStrong B A (a::tr).

Lemma ia_strong : forall A B tr,
  ImmAfterStrong B A tr ->
  ImmAfter _ _ _ COMPTDEC B A tr.
Proof.
  intros A B tr Hias.
  destruct Hias.
    constructor.
    auto.
Qed.
*)
Lemma immafter_no_match : forall B A tr tr',
  ImmAfter PAYD COMPT COMPS COMPTDEC B A tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC A a) ->
  ImmAfter _ _ _ COMPTDEC B A (tr' ++ tr).
Proof.
  unfold ImmAfter.
  intros B A tr tr' Hia Hno_match.
  rewrite List.rev_app_distr.
  apply IB_compose; auto.
  induction tr'.
    simpl. constructor.

    simpl. apply IB_compose.
      apply IB_nB.
        constructor.

        apply Hno_match. simpl. auto.

      apply IHtr'. intros a0 Hina0.
      apply Hno_match. simpl. auto.
Qed.

(*Lemma immafter_no_match : forall B A tr tr',
  ImmAfterStrong B A tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC A a) ->
  ImmAfterStrong B A (tr' ++ tr).
Proof.
  intros B A tr tr' Hias Hno_match.
  induction tr'.
    auto.

    simpl. apply IAS_cons.
      cut (ImmAfterStrong B A (tr' ++ tr)).
        intro Hias'. destruct Hias'.
          constructor.

          apply IA_nA; eauto.
          
        apply IHtr'. intros a0 Hina0.
        apply Hno_match. simpl. auto.

        apply Hno_match. simpl. auto.
Qed.*)

Lemma no_before_IA_init : forall init input B A s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) A ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   ImmAfter _ _ _ COMPTDEC B A tr.
Proof.
  intros. rewrite <- List.app_nil_r.
  apply immafter_no_match.
    constructor.

    eapply no_match_init; eauto.
Qed.

Lemma no_before_IA_hdlr : forall c m input B A s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) A ->
  not_recv_match (comp_type _ _ c) (tag _ m) A ->
  not_select_match (comp_type _ _ c) A ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   ImmAfter _ _ _ COMPTDEC B A tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   ImmAfter _ _ _ COMPTDEC B A tr.
Proof.
  intros.
  eapply no_match_hdlr; eauto.
  apply immafter_no_match.
Qed.

Lemma disables_no_match : forall oact oact' tr tr',
  Disables PAYD COMPT COMPS COMPTDEC oact oact' tr ->
  (forall a, List.In a tr' ->
             ~ActionMatch.AMatch _ _ _ COMPTDEC oact' a) ->
  Disables _ _ _ COMPTDEC oact oact' (tr' ++ tr).
Proof.
  intros oact oact' tr tr' Hen Hno_match.
  induction tr'.
    auto.

    apply D_not_disablee. apply IHtr'.
      intros a0 Hina0.
      apply Hno_match. simpl. auto.

      apply Hno_match. simpl. auto.
Qed.

Lemma no_disablee_init : forall init input oact oact' s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) oact' ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Disables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros. rewrite <- List.app_nil_r.
  apply disables_no_match.
    constructor.

    eapply no_match_init; eauto.
Qed.

Lemma no_disablee_hdlr : forall c m input oact oact' s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) oact' ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact' ->
  not_select_match (comp_type _ _ c) oact' ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Disables PAYD COMPT COMPS COMPTDEC oact oact' tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   Disables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros.
  eapply no_match_hdlr; eauto.
  apply disables_no_match.
Qed.

Lemma no_disabler_init : forall init input oact s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match (proj1_sig init) oact ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   forall act,
     List.In act tr ->
     ~ActionMatch.AMatch _ _ _ COMPTDEC oact act.
Proof.
  intros. eapply no_match_init; eauto.
Qed.

Lemma no_disabler_hdlr : forall c m input oact s s' act,
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (proj1_sig (projT2 (HANDLERS (tag _ m) (comp_type _ _ c)))) oact ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact ->
  not_select_match (comp_type _ _ c) oact ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
     List.In act tr ->
     ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
     ~ActionMatch.AMatch _ _ _ COMPTDEC oact act) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
    List.In act tr ->
    ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
    ~ActionMatch.AMatch _ _ _ COMPTDEC oact act.
Proof.
  intros. revert H4.
  eapply no_match_hdlr with
  (P:=fun tr => List.In act tr -> ~ActionMatch.AMatch _ _ _ COMPTDEC oact act);
    eauto.
  intros. apply List.in_app_or in H7.
  destruct H7; eauto.
Qed.

End PolLangFacts.