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
  | Reflex.StUpd _ _ _ => True
  | Reflex.CompLkup _ _ c1 c2 =>
    no_match c1 oact /\
    no_match c2 oact
  | Reflex.Nop _ => True
  end.

(*Lemma enables_initial_init_state : forall oact,
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
  no_match init oact ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   forall act, List.In act tr ->
               ~ActionMatch.AMatch PAYD COMPT COMPS COMPTDEC oact act.
Proof.
  intros init input oact s Hinit Hno_en tr Htr act Hin.
  inversion Hinit. clear Hinit.
  subst s0. subst s. simpl in *.
  generalize dependent tr.
  pose proof (enables_initial_init_state oact).
  generalize dependent (initial_init_state PAYD COMPT COMPS KSTD IENVD).
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
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o. destruct o0.
    destruct c. simpl. unfold match_comp'.
    destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
    simpl. destruct x. subst ct. simpl in *.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct o. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    simpl. unfold match_comp'.
    destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
    simpl. destruct x. subst ct. simpl in *.
    destruct c; destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; tauto.
    destruct o0. destruct o. simpl. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    contradiction.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o1; try contradiction.
    destruct c. simpl.
    destruct (COMPTDEC t conc_pat_type); try tauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
        => destruct e
    end.
    simpl in *.
      eapply IHinit1; eauto; simpl; auto.
      eapply IHinit2; eauto.
  *)

Lemma no_enablee_init : forall init input oact oact' s,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init input s ->
  no_match init oact' ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Admitted.
(*Proof.
  intros init input oact oact' s Hinit Hno_en tr Htr.
  inversion Hinit. clear Hinit.
  subst s0. subst s. simpl in *.
  generalize dependent tr.
  pose proof (enables_initial_init_state oact oact').
  generalize dependent (initial_init_state PAYD COMPT COMPS KSTD IENVD).
  induction init; simpl in *; intros; auto.
    destruct input as [input1 input2]. simpl in *.
    destruct Hno_en as [Hno_en1 Hno_en2].
    specialize (IHinit1 input1 Hno_en1 i H).
    apply (IHinit2 input2 Hno_en2
           (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd i init1
                input1)); auto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ if ?e then _ else _ ] |- _ ]
        => destruct e
    end.
      eapply IHinit2; eauto.
      eapply IHinit1; eauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i).
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o. destruct o0.
    destruct c. simpl. unfold match_comp'.
    destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
    simpl. destruct x. subst ct. simpl in *.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct o. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    simpl. unfold match_comp'.
    destruct (eval_base_expr COMPT COMPS (init_env PAYD COMPT COMPS KSTD envd i) e).
    simpl. destruct x. subst ct. simpl in *.
    destruct c; destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; tauto.
    destruct o0. destruct o. simpl. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    contradiction.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o1; try contradiction.
    destruct c. simpl.
    destruct (COMPTDEC t conc_pat_type); try tauto.

    destruct (init_ktr PAYD COMPT COMPS KSTD envd i0).
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
        => destruct e
    end.
    simpl in *.
      eapply IHinit1; eauto; simpl; auto.
      eapply IHinit2; eauto.
Qed.*)

(*
Lemma no_enablee_hdlr' : forall c m oact oact',
  let hdlrs := HANDLERS (tag _ m) (comp_type _ _ c) in
  forall s s' input,
  hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m
    (projT1 hdlrs) s (projT2 hdlrs) input = s' ->
  no_enablee (projT2 hdlrs) oact' ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s) = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s') = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Proof.
  intros c m oact oact' hdlrs s s' input Hrun Hno_en Hind tr Htr.
  destruct hdlrs as [envd cmd]. simpl in *. subst s'.
  generalize dependent tr.
  induction cmd; simpl in *; intros; auto.
    destruct input as [input1 input2]. simpl in *.
    destruct Hno_en as [Hno_en1 Hno_en2].
    specialize (IHcmd1 s input1 Hno_en1 Hind).
    eapply IHcmd2; eauto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    match goal with
    | [ _ : context [ if ?e then _ else _ ] |- _ ]
        => destruct e
    end.
      eapply IHcmd2; eauto.
      eapply IHcmd1; eauto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o. destruct o0.
    destruct c0. simpl. unfold match_comp'.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
           (kst PAYD COMPT COMPS KSTD s) env e).
    simpl. destruct x. subst ct. simpl in *.
    destruct (COMPTDEC comp_type conc_pat_type); try tauto.
    destruct o. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    simpl. unfold match_comp'.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
           (kst PAYD COMPT COMPS KSTD s) env e).
    simpl. destruct x. subst ct. simpl in *.
    destruct c0; destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; tauto.
    destruct o0. destruct o. simpl. unfold msgMatch'. simpl.
    destruct (fin_eq_dec t opt_tag); try contradiction; tauto.
    contradiction.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto. destruct o1; try contradiction.
    destruct c0. simpl.
    destruct (COMPTDEC t conc_pat_type); try tauto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. apply E_not_future; auto.
    destruct oact'; auto.

    destruct s as [s env]. destruct (ktr _ _ _ _ s) as [ ? ]_eqn.
    simpl in *. apply pack_injective in Htr.
    subst tr. auto.

    destruct Hno_en as [Hno_en1 Hno_en2].
    destruct s as [s env].
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
        => destruct e
    end.
    simpl in *.
      eapply IHcmd1; eauto; simpl; auto.
      eapply IHcmd2; eauto.
Qed.*)

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
  
Lemma no_enablee_hdlr : forall c m input oact oact' s s',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input s s' ->
  no_match (projT2 (HANDLERS (tag _ m) (comp_type _ _ c))) oact' ->
  not_recv_match (comp_type _ _ c) (tag _ m) oact' ->
  not_select_match (comp_type _ _ c) oact' ->
  (forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr) ->
  forall tr : Reflex.KTrace PAYD COMPT COMPS,
   ktr PAYD COMPT COMPS KSTD s' = inhabits tr ->
   Enables PAYD COMPT COMPS COMPTDEC oact oact' tr.
Admitted.
(*Proof.
  intros c m input oact oact' s s' Hve Hno_en
         Hno_recv Hno_select Hind tr Htr.
  inversion Hve. unfold kstate_run_prog in *.
  clear Hve. subst s'0. subst s'. clear H2 H.
  eapply no_enablee_hdlr'; eauto.
  clear dependent tr. simpl. intros tr Htr.
  apply pack_injective in Htr; subst tr.
  apply E_not_future; auto.
  apply E_not_future; auto.
  destruct oact'; auto. simpl in *.
  destruct o; destruct o0; try contradiction;
  destruct c0; simpl; destruct c; simpl in *;
  destruct (COMPTDEC comp_type conc_pat_type);
    try contradiction; try tauto.

  destruct oact'; auto. simpl in *.
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
Qed.*)

End PolLangFacts.