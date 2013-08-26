Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import List.
Require Import Ynot.
Require Import Coq.Logic.Eqdep.
Require Import ProofIrrelevance.

Section NI.

Context {NB_MSG : nat}.
Variable PAYD     : vvdesc NB_MSG.
Variable COMPT    : Set.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Variable COMPS    : COMPT -> compd.
Variable IENVD    : vcdesc COMPT.
Variable KSTD     : vcdesc COMPT.
Variable INIT : init_prog PAYD COMPT COMPS KSTD IENVD.
Variable HANDLERS : handlers PAYD COMPT COMPS KSTD.
Definition comp := comp COMPT COMPS.
Definition Reach := Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition KAction := KAction PAYD COMPT COMPS.
Definition kstate := kstate PAYD COMPT COMPS KSTD.
Definition ktr := ktr PAYD COMPT COMPS KSTD.

Definition is_input labeler (act : KAction) :=
  match act with
  | KRecv c _ => labeler c
  | KBogus c _ => labeler c
  | _        => false
  end.

Definition is_output labeler (act : KAction) :=
  match act with
  | KSend c _   => labeler c
  | KExec _ _ c => labeler c
  | _           => false
  end.

Definition inputs labeler (tr : KTrace) :=
  filter (is_input labeler) tr.

Definition outputs labeler (tr : KTrace) :=
  filter (is_output labeler) tr.

Definition KCall := KCall PAYD COMPT COMPS.
Definition KExec := KExec PAYD COMPT COMPS.
Definition KRecv := KRecv PAYD COMPT COMPS.

Definition vars_eq (s1 s2 : kstate)
  (lblr : fin (projT1 KSTD) -> bool) :=  
  shvec_erase _ lblr _ (kst _ _ _ _ s1) = shvec_erase _ lblr _ (kst _ _ _ _ s2).

Definition high_in_eq (s s' : kstate) clblr :=
  forall tr tr',
    ktr s = [tr]%inhabited ->
    ktr s' = [tr']%inhabited ->
    inputs clblr tr = inputs clblr tr'.

Definition high_out_eq (s s' : kstate) clblr :=
  forall tr tr',
    ktr s = [tr]%inhabited ->
    ktr s' = [tr']%inhabited ->
    outputs clblr tr = outputs clblr tr'.

Definition low_in_nil (s : kstate) clblr :=
  forall tr,
    ktr s = [tr]%inhabited ->
    inputs (fun c => negb (clblr c)) tr = nil.

Definition NI clblr vlblr := forall s,
  Reach s ->
  (exists snil,
    Reach snil /\
    high_in_eq s snil clblr /\
    low_in_nil snil clblr /\
    high_out_eq s snil clblr /\
    vars_eq s snil vlblr).

Definition low_ok clblr vlblr := forall c m i s s',
  clblr c = false ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s s' ->
  high_out_eq s s' clblr /\
  vars_eq s s' vlblr.

Definition high_ok clblr vlblr :=
  forall c m i s1 s1' s2 s2',
    clblr c = true ->
    high_out_eq s1 s2 clblr ->
    vars_eq s1 s2 vlblr ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s1 s1' ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s2 s2' ->
    high_out_eq s1' s2' clblr /\ vars_eq s1' s2' vlblr.

Ltac uninhabit :=
  match goal with
  | [ H : [_]%inhabited = [?tr]%inhabited |- _ ]
    => apply pack_injective in H; subst tr
  end.

Lemma init_inputs_nil : forall init i s tr lblr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init i s ->
  ktr s = [tr]%inhabited ->
  inputs lblr tr = nil.
Proof.
  intros init i s tr lblr HInit Htr.
  destruct HInit; subst s;
  generalize dependent tr.
  case_eq (init_ktr _ _ _ _ _ (initial_init_state PAYD COMPT COMPS KSTD IENVD)).
  intros k Htri.
  assert (inputs lblr k = nil) by
      (simpl in Htri; apply pack_injective in Htri; rewrite <- Htri; auto).
  generalize dependent k.
  generalize dependent (initial_init_state PAYD COMPT COMPS KSTD IENVD).
  induction init; intros ist k Htri H tr Htr; simpl in *;
    try (destruct ist; destruct init_ktr as [k']; simpl in *;
    apply pack_injective in Htr; subst tr; apply pack_injective in Htri;
    subst k'; auto).

    destruct i as [i1 i2].
    simpl in *.
    case_eq (init_ktr _ _ _ _ _
               (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd ist init1 i1));
    intros.
    apply IHinit2 with
      (i:=i2)
      (i0:=(init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd ist init1 i1))
      (k:=k0); auto.
    apply IHinit1 with (i:=i1) (i0:=ist) (k:=k); auto.

    match goal with
    | [ _ : context[if ?e then _ else _] |- _ ]
        => destruct e
    end. 
    eapply IHinit2 with (i:=(snd i)) (i0:=ist); eauto.
    eapply IHinit1 with (i:=(fst i)) (i0:=ist); eauto.

    (*CompLkup*)
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
      => destruct e
    end; simpl in *; eauto.
    (*component found case*)
    match goal with
    | [ _ : context [ init_state_run_cmd _ _ _ _ _ _ ?s _ ?ipt ] |- _ ]
      => eapply IHinit1 with (i:=ipt) (i0:=s); eauto
    end.
Qed.

Lemma hdlr_no_recv :
  forall c m envd (hst:hdlr_state PAYD COMPT COMPS KSTD envd) stmt i tr tr' lblr,
  ktr (hdlr_kst _ _ _ _ _ hst) = [tr]%inhabited ->
  ktr (hdlr_kst _ _ _ _ _
    (hdlr_state_run_cmd _ _ COMPTDEC _ _ c m _ hst stmt i))
  = [tr']%inhabited ->
  exists tr'', tr' = tr'' ++ tr /\
               forall act, In act tr'' ->
                           is_input lblr act = false.
Proof.
  intros.
  generalize dependent hst.
  generalize dependent tr.
  generalize dependent tr'.
  induction stmt; intros tr' tr hst.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    exists nil.
    rewrite H in H0.
    apply pack_injective in H0.
    split; auto.
    intros.
    simpl in *.
    contradiction.

    intros.
    simpl in *.
    destruct i as [i1 i2].
    case_eq (ktr
              (hdlr_kst PAYD COMPT COMPS KSTD envd
                 (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                    hst stmt1 i1))); intros.
    pose proof (IHstmt1 i1 k tr hst H H1).
    pose (hst1:=hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                    hst stmt1 i1).
    destruct hst as [hkst henv].
    destruct hkst.
    pose proof (IHstmt2 i2 tr' k hst1 H1 H0).
    destruct H2.
    destruct H2.
    destruct H3.
    destruct H3.
    exists (x0++x).
    split.
      subst tr'.
      subst k.
      symmetry.
      apply app_ass.

      intros.
      apply in_app_or in H6.
      destruct H6.
      apply H5; auto.
      apply H4; auto.

    intros.
    destruct hst as [hkst henv]_eqn.
    destruct hkst.
    simpl in *.
    destruct i as [i1 i2].
    match goal with
    | [ _ : context[if ?e then _ else _] |- _ ]
      => destruct e
    end; [apply IHstmt2 with (i:=i2) (hst:=hst) | apply IHstmt1 with (i:=i1) (hst:=hst)];
    subst hst; auto.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr0.
    simpl in *.
    apply pack_injective in H0.
    subst tr'.
    apply pack_injective in H.
    subst k.
    match goal with
    |- exists _, (?act::_) = _ ++ _ /\ _
      => exists (act::nil)
    end.
    split; auto.
    intros.
    simpl in *.
    destruct H.
      subst act; auto.
      contradiction.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr0.
    simpl in *.
    apply pack_injective in H0.
    subst tr'.
    apply pack_injective in H.
    subst k.
    match goal with
    |- exists _, (?act::_) = _ ++ _ /\ _
      => exists (act::nil)
    end.
    split; auto.
    intros.
    simpl in *.
    destruct H.
      subst act; auto.
      contradiction.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr0.
    simpl in *.
    apply pack_injective in H0.
    subst tr'.
    apply pack_injective in H.
    subst k.
    match goal with
    |- exists _, (?act::_) = _ ++ _ /\ _
      => exists (act::nil)
    end.
    split; auto.
    intros.
    simpl in *.
    destruct H.
      subst act; auto.
      contradiction.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr0.
    simpl in *.
    apply pack_injective in H0.
    subst tr'.
    apply pack_injective in H.
    subst k.
    exists nil.
    split; auto.
    intros.
    simpl in *.
    contradiction.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
      => destruct e
    end; simpl in *.
      match goal with
      | [ _ : context [ hdlr_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?s ?j ?input ] |- _ ]
        => destruct (hdlr_state_run_cmd a b c d e f g h s j input) as [ks'' new_env]_eqn;
           eapply IHstmt1 with (i:=input) (hst:=s); eauto
      end. rewrite Heqh. auto.

      eapply IHstmt2; eauto.
      simpl; assumption.
Qed.


Lemma ve_inputs_high : forall c m i s s' tr tr' lblr,
  lblr c = true ->
  ktr s = [tr]%inhabited ->
  ktr s' = [tr']%inhabited ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s s' ->
  inputs lblr tr' = KRecv c m :: (inputs lblr tr).
Proof.
  intros c m i s s' tr tr' lblr Hhigh Htr Htr' Hve.
  inversion Hve.
  unfold kstate_run_prog in H2.
  apply f_equal with (f:=ktr) in H0.
  simpl in H0.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt ?i) = _,
      Hmid : ktr _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt i trmid tr' lblr Hmid)
  end.
  subst s'.
  apply H3 in Htr'.
  destruct Htr'.
  destruct H2.
  subst tr'.
  match goal with
  |- inputs ?lblr (?x++?act1::?act2::?tr0) = _
    => replace (inputs lblr (x++act1::act2::tr0)) with
       (inputs lblr (act1::act2::tr0))
  end.
  simpl.
  unfold ktr in Htr.
  rewrite H in Htr.
  apply pack_injective in Htr.
  subst tr.
  rewrite Hhigh.
  auto.
  clear H3.
  induction x.
    auto.

    simpl in *.
    rewrite Hhigh in *.
    pose proof (H4 a).
    simpl in H2.
    pose proof (H2 (or_introl _ (Logic.eq_refl a))).
    rewrite H3.
    apply IHx; auto.
Qed.

Lemma ve_inputs_low : forall c m i s s' tr tr' lblr,
  lblr c = false ->
  ktr s = [tr]%inhabited ->
  ktr s' = [tr']%inhabited ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s s' ->
  inputs lblr tr' = inputs lblr tr.
Proof.
  intros c m i s s' tr tr' lblr Hhigh Htr Htr' Hve.
  inversion Hve.
  unfold kstate_run_prog in H2.
  apply f_equal with (f:=ktr) in H0.
  simpl in H0.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt ?i) = _,
      Hmid : ktr _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt i trmid tr' lblr Hmid)
  end.
  subst s'.
  apply H3 in Htr'.
  destruct Htr'.
  destruct H2.
  subst tr'.
  match goal with
  |- inputs ?lblr (?x++?act1::?act2::?tr0) = _
    => replace (inputs lblr (x++act1::act2::tr0)) with
       (inputs lblr tr0)
  end.
  unfold ktr in Htr.
  rewrite H in Htr.
  apply pack_injective in Htr.
  subst tr.
  auto.

  induction x.
    simpl.
    rewrite Hhigh.
    auto.

    simpl in *.
    pose proof (H4 a).
    simpl in H2.
    pose proof (H2 (or_introl _ (Logic.eq_refl a))).
    rewrite H5.
    apply IHx; eauto.
Qed.

Theorem ni_suf : forall clblr vlblr,
  low_ok clblr vlblr ->
  high_ok clblr vlblr ->
  NI clblr vlblr.
Proof.
  unfold NI.
  intros clblr vlblr Hlow Hhigh s HReach.
  induction HReach.
    exists s.
      split. econstructor; eauto.

      split. unfold high_in_eq. intros tr tr' Hktr Hktr'.
      rewrite Hktr' in Hktr. apply pack_injective in Hktr.
      subst tr. reflexivity.

      split. unfold low_in_nil. intros.
      eapply init_inputs_nil; eauto.

      split. unfold high_in_eq. intros tr tr' Hktr Hktr'.
      rewrite Hktr' in Hktr. apply pack_injective in Hktr.
      subst tr. reflexivity.

      reflexivity.

    destruct IHHReach as [snil_ind IHsnil].
    case_eq (clblr c); intro Hclblr.
      match goal with
      | [ H : ValidExchange _ _ _ _ _ _ _ _ _ _ _ |- _ ]
        => inversion H
      end.
      destruct snil_ind as [csnil [trnil] stnil fdnil]_eqn.
      set (snil_next := kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m 
         (projT1 hdlrs) (mk_inter_ve_st _ _ _ _ c m snil_ind trnil)
         (projT2 hdlrs) input).
      exists snil_next; unfold snil_next.
(*      exists (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m 
         (projT1 hdlrs) (mk_inter_ve_st _ _ _ _ c m snil_ind trnil)
         (projT2 hdlrs) input).*)
      assert (ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m input snil_ind
        (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m 
          (projT1 hdlrs)
          (mk_inter_ve_st PAYD COMPT COMPS KSTD c m snil_ind trnil)
          (projT2 hdlrs) input)) as Hve.
        econstructor; eauto; subst snil_ind; eauto.

        split.
        eapply (Reach_valid _ _ _ _ _ _ _ _ c m input snil_ind); eauto.
          subst snil_ind; eapply IHsnil.
        
        split.
        unfold high_in_eq. intros.
        destruct s as [css [trs] sts fds].
        erewrite ve_inputs_high with (tr':=tr0) (tr:=trs) (s':=s') (m:=m); eauto.
        erewrite ve_inputs_high with (tr':=tr') (tr:=trnil) (m:=m); eauto.
        f_equal. eapply IHsnil; eauto.
        subst snil_ind; auto.
        simpl; auto.
        subst s'; auto.

        split.
        unfold low_in_nil; intros.
        rewrite ve_inputs_low with (tr:=trnil) (tr':=tr0) (m:=m) (c:=c) (i:=input)
          (s:=snil_ind) (s':=snil_next); auto.
        eapply IHsnil; eauto.
        rewrite Hclblr; auto.
        subst snil_ind; auto.

        eapply Hhigh with (s1:=s) (s2:=snil_ind) (c:=c) (i:=input); eauto;
          try solve [subst snil_ind; eapply IHsnil; eauto | subst s'; auto].

      exists snil_ind.
        split.
        eapply IHsnil; eauto.

        split.
        unfold high_in_eq. intros.
        destruct s as [css [trs] sts fds].
        erewrite ve_inputs_low with (tr:=trs) (tr':=tr) (m:=m) (c:=c) (i:=input)
          (s':=s'); eauto.
        eapply IHsnil; eauto.
        simpl; auto.

        split.
        eapply IHsnil; eauto.

        unfold low_ok in Hlow.
        pose proof (Hlow c m input s s' Hclblr H) as Hss'.
        unfold high_out_eq in *. unfold vars_eq in *.
        destruct snil_ind as [csnil [trnil] stnil fdnil]_eqn.
        split.
          intros.
          destruct s. destruct ktr0.
          assert (outputs clblr k = outputs clblr tr) as Heq.
             eapply Hlow; eauto.
          rewrite <- Heq.
          eapply IHsnil; eauto.

          assert (shvec_erase (sdenote_cdesc COMPT COMPS) vlblr (projT2 KSTD)
            (kst PAYD COMPT COMPS KSTD s) =
            shvec_erase (sdenote_cdesc COMPT COMPS) vlblr (projT2 KSTD)
            (kst PAYD COMPT COMPS KSTD s')) as Heq.
            eapply Hlow; eauto.
          rewrite <- Heq.
          eapply IHsnil; eauto.

    match goal with
    | [ H : BogusExchange _ _ _ _ _ _ _ _ |- _ ]
      => inversion H
    end.
    destruct IHHReach as [snil_ind IHsnil].
    case_eq (clblr c); intro Hlblr.
      destruct snil_ind as [csnil [trnil] stnil fdnil]_eqn.
      exists (mk_bogus_st PAYD COMPT COMPS KSTD c bmsg snil_ind trnil).
        split.
        eapply (Reach_bogus _ _ _ _ _ _ _ _ snil_ind _ c bmsg); eauto.
        subst snil_ind; eapply IHsnil; eauto.
        econstructor; eauto.
        subst snil_ind; auto.

        split.
        unfold mk_bogus_st.
        unfold high_in_eq. intros.
        simpl in *. repeat uninhabit. simpl.
        rewrite Hlblr.
        f_equal. eapply IHsnil; eauto.

        split.
        unfold mk_bogus_st.
        unfold low_in_nil. intros.
        simpl in *. uninhabit. simpl.
        rewrite Hlblr. simpl.
        eapply IHsnil; eauto.

        split.
        unfold mk_bogus_st.
        unfold high_out_eq. intros.
        simpl in *. repeat uninhabit. simpl.
        eapply IHsnil; eauto.

        unfold mk_bogus_st. simpl.
        subst snil_ind; eapply IHsnil; eauto.

      exists snil_ind.
        split.
        eapply IHsnil; eauto.

        split.
        unfold mk_bogus_st.
        unfold high_in_eq. intros.
        simpl in *. repeat uninhabit. simpl.
        rewrite Hlblr.
        eapply IHsnil; eauto.

        split.
        unfold mk_bogus_st.
        unfold low_in_nil. intros.
        simpl in *.
        eapply IHsnil; eauto.

        split.
        unfold mk_bogus_st.
        unfold high_out_eq. intros.
        simpl in *. repeat uninhabit. simpl.
        eapply IHsnil; eauto.

        unfold mk_bogus_st. simpl.
        eapply IHsnil; eauto.
Qed.

End NI.