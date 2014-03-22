Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import Eqdep.
Require Import ProofIrrelevance.

Section WITH_SPEC.

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

Definition desc_eq (d:desc) : forall (x y:s[[d]]), decide (x = y) :=
  match d with
  | num_d => num_eq
  | str_d => str_eq
  | fd_d => fd_eq
  end.

Lemma comp_eq : forall (c1 c2:comp), decide (c1 = c2).
Proof.
  intros c1 c2. destruct c1 as [ct1 fd1 cfg1]. destruct c2 as [ct2 fd2 cfg2].
  assert (decide (ct1 = ct2)) as Hcteq_dec by exact (COMPTDEC ct1 ct2).
  destruct Hcteq_dec.
    assert (decide (fd1 = fd2)) as Hfdeq_dec by exact (fd_eq fd1 fd2).
      destruct Hfdeq_dec.
        subst ct1.
        assert (decide (cfg1 = cfg2)) as Hcfgeq_dec.
          destruct (comp_conf_desc COMPT COMPS ct2) as [n v].
          induction n.
            simpl in *. destruct v. unfold sdenote_vdesc in *.
            simpl in *. destruct cfg1; destruct cfg2. auto.

            simpl in *. destruct v. unfold sdenote_vdesc in *.
            simpl in *. destruct cfg1 as [e1 cfg1']. destruct cfg2 as [e2 cfg2'].
            assert (decide (e1 = e2)) as Helteq_dec by exact (desc_eq d e1 e2).
            destruct Helteq_dec.
              pose proof (IHn v cfg1' cfg2') as Heq_dec'.
              destruct Heq_dec'.
                subst e1. subst cfg1'. auto.

                right; unfold not; intro Heq; inversion Heq; auto.

              right; unfold not; intro Heq; inversion Heq; auto.
            
        destruct Hcfgeq_dec.
          subst fd1. subst cfg1. auto.

          right. unfold not. intro Heq. inversion Heq.
          apply inj_pairT2 in H1. auto.

        right; unfold not; intro Heq; inversion Heq; auto.

    right; unfold not; intro Heq; inversion Heq; auto.
Defined.

Definition var_eq (d : cdesc COMPT) :
  forall (x y : sdenote_cdesc COMPT COMPS d), decide (x = y).
Proof.
  intros.
  destruct d.
    exact (desc_eq d x y).

    simpl in *.
    destruct x as [c1 cpf1]; destruct y as [c2 cpf2].
    assert (decide (c1 = c2)) as Heqc_dec by exact (comp_eq c1 c2).
    destruct Heqc_dec.
      subst c1.
      assert (cpf1 = cpf2) by apply proof_irrelevance.
      subst cpf1. auto.

      right. unfold not. intro H. inversion H. auto.
Qed.

End WITH_SPEC.

(*
Lemma init_st_same : forall s1 s2,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s1 ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s2 ->
  s1 = s2.
Proof.
  intros s1 s2 HI1 HI2.
  destruct HI1 as [s1' in1 Hs1'].
  destruct HI2 as [s2' in2 Hs2'].
  rewrite <- Hs1' in Hs2'.
  rewrite Hs2'.
  reflexivity.
Qed.

Lemma init_tr_same : forall s1 s2 tr1 tr2,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s1 ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s2 ->
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  tr1 = tr2.
Proof.
  intros s1 s2 tr1 tr2 HI1 HI2 Htr1 Htr2.
  assert (s1 = s2) as Heq by (apply init_st_same; auto).
  subst s1.
  rewrite Htr1 in Htr2.
  apply pack_injective in Htr2.
  assumption.
Qed.

Lemma init_vars_eq : forall s1 s2 lblr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s1 ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s2 ->
  vars_eq s1 s2 lblr.
Proof.
  intros s1 s2 lblr HI1 HI2.
  assert (s1 = s2) as Heq by (apply init_st_same; auto).
  subst s1. unfold vars_eq. reflexivity.
Qed.

Lemma init_inputs_nil : forall init s tr lblr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init s ->
  ktr _ _ _ _ s = [tr]%inhabited ->
  inputs lblr tr = nil.
Proof.
  intros init s tr lblr HInit Htr.
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

    case_eq (init_ktr _ _ _ _ _
               (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd ist init1));
    intros.
    apply IHinit2 with
      (i:=(init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd ist init1))
      (k:=k0); auto.
    apply IHinit1 with (i:=ist) (k:=k); auto.
    destruct ist; auto.

    match goal with
    | [ _ : context[if ?e then _ else _] |- _ ]
        => destruct e;
           match goal with
           | [ _ : Reflex.init_ktr _ _ _ _ _ (init_state_run_cmd _ _ _ _ _ _ ?s _) = _ |- _ ]
             => solve [eapply IHinit2 with (i:=s); eauto |
                       eapply IHinit1 with (i:=s); eauto]
           end
    end. 

    (*Send all*)
    induction init_comps; auto; simpl in *.
      match goal with
      |- context[ if ?e then _ else _ ]
         => destruct e
      end; auto.

    (*CompLkup*)
    match goal with
    | [ _ : context [ match ?e with | Some _ => _ | None => _ end ] |- _ ]
      => destruct e
    end; simpl in *; eauto.
    (*component found case*)
    match goal with
    | [ _ : context [ init_state_run_cmd _ _ _ _ _ _ ?s _ ] |- _ ]
      => eapply IHinit1 with (i:=s); eauto
    end.
Qed.

Lemma hdlr_no_recv :
  forall c m envd (hst:hdlr_state PAYD COMPT COMPS KSTD envd) stmt tr tr' lblr,
  ktr _ _ _ _ (hdlr_kst _ _ _ _ _ hst) = [tr]%inhabited ->
  ktr _ _ _ _ (hdlr_kst _ _ _ _ _
    (hdlr_state_run_cmd _ _ COMPTDEC _ _ c m _ hst stmt))
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
    case_eq (ktr PAYD COMPT COMPS KSTD
              (hdlr_kst PAYD COMPT COMPS KSTD envd
                 (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                    hst stmt1))); intros.
    pose proof (IHstmt1 k tr hst H H1).
    pose (hst1:=hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                    hst stmt1).
    destruct hst as [hkst henv].
    destruct hkst.
    pose proof (IHstmt2 tr' k hst1 H1 H0).
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
    match goal with
    | [ _ : context[if ?e then _ else _] |- _ ]
      => destruct e
    end; [apply IHstmt2 with (hst:=hst) | apply IHstmt1 with (hst:=hst)];
    subst hst; auto.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr.
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
    destruct hst as [hkst henv].
    destruct hkst.
    generalize dependent tr'.
    induction kcs; intros.
      destruct ktr; simpl in *.
      exists nil.
      apply pack_injective in H; subst tr.
      apply pack_injective in H0; subst tr'.
      split; auto.
      intros; simpl in *; contradiction.

      simpl in *.
      match goal with
      | [ _ : context[ if ?e then _ else _ ] |- _ ]
          => destruct e
      end; try solve [apply IHkcs; auto].
      destruct ktr.
      simpl in *.
      apply pack_injective in H0; subst tr'.
      match goal with
      | [ _ : _ -> forall _, [?tr0]%inhabited = _ -> _ |- _ ]
          => pose proof (IHkcs H tr0 (Logic.eq_refl [tr0]%inhabited))
      end.
      destruct H0.
      exists (KSend PAYD COMPT COMPS a
       {|
       tag := t;
       pay := eval_hdlr_payload_expr PAYD COMPT COMPS KSTD c m kst envd henv
                (lkup_tag PAYD t) p |}::x).
      destruct H0.
      split.
        rewrite <- app_comm_cons.
        f_equal.
        assumption.

        intros.
        simpl in *.
        destruct H2; auto.
        subst act; auto.

    intros.
    destruct hst as [hkst henv];
    destruct hkst; intros; simpl in *.
    destruct ktr.
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
    destruct ktr.
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
    destruct ktr.
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
      | [ _ : context [ hdlr_state_run_cmd ?a ?b ?c ?d ?e ?f ?g ?h ?s ?j ] |- _ ]
        => destruct (hdlr_state_run_cmd a b c d e f g h s j) as [ks'' new_env]_eqn;
           apply IHstmt1 with (hst:=s); eauto
      end. rewrite Heqh. auto.

      eapply IHstmt2; eauto.
      simpl; assumption.
Qed.


Lemma ve_inputs_high : forall c m s s' tr tr' lblr,
  lblr c = true ->
  ktr _ _ _ _ s = [tr]%inhabited ->
  ktr _ _ _ _ s' = [tr']%inhabited ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s s' ->
  inputs lblr tr' = KRecv c m :: (inputs lblr tr).
Proof.
  intros c m s s' tr tr' lblr Hhigh Htr Htr' Hve.
  inversion Hve.
  unfold kstate_run_prog in H2.
  apply f_equal with (f:=ktr PAYD COMPT COMPS KSTD) in H0.
  simpl in H0.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt) = _,
      Hmid : ktr _ _ _ _ _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt trmid tr' lblr Hmid)
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

Lemma ve_inputs_low : forall c m s s' tr tr' lblr,
  lblr c = false ->
  ktr _ _ _ _ s = [tr]%inhabited ->
  ktr _ _ _ _ s' = [tr']%inhabited ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s s' ->
  inputs lblr tr' = inputs lblr tr.
Proof.
  intros c m s s' tr tr' lblr Hhigh Htr Htr' Hve.
  inversion Hve.
  unfold kstate_run_prog in H2.
  apply f_equal with (f:=ktr PAYD COMPT COMPS KSTD) in H0.
  simpl in H0.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt) = _,
      Hmid : ktr _ _ _ _ _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt trmid tr' lblr Hmid)
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

Lemma ve_tr_sub : forall c m s s' tr tr',
  ktr _ _ _ _ s = [tr]%inhabited ->
  ktr _ _ _ _ s' = [tr']%inhabited ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s s' ->
  exists tr'', tr' = tr'' ++ tr.
Proof.
  intros.
  inversion H1.
  unfold kstate_run_prog in *.
  apply f_equal with (f:=ktr _ _ _ _) in H3; simpl in H3.
  subst s'.
  pose proof (hdlr_no_recv _ _ _ (default_hdlr_state PAYD COMPT COMPS KSTD s'0 (projT1 hdlrs))
    (projT2 hdlrs) _ _ (fun _ => true) H3 H0).
  destruct H5.
  exists (x ++ (Reflex.KRecv PAYD COMPT COMPS c m
        :: KSelect PAYD COMPT COMPS cs c :: nil)).
  rewrite H2 in H. apply pack_injective in H. subst tr.
  destruct H5.
  subst tr'.
  rewrite app_ass.
  auto.
Qed.    

Ltac high_ins :=
  match goal with
  | [ ce : Reflex.comp _ _, me : msg _ |- _]
      => match goal with
         | [ _ : ValidExchange _ _ _ _ _ _ ce me ?sb ?sa,
             _ : ktr _ _ _ _ ?sa = [?tra]%inhabited,
             Hin : context[inputs _ ?tra] |- _ ]
             => let cs := fresh "cs" in
                let itr := fresh "itr" in
                let trb := fresh "tr" in
                let st := fresh "st" in
                let fd := fresh "fd" in
                destruct sb as [cs itr st fd]_eqn; destruct itr as [trb];
                rewrite ve_inputs_high with (c:=ce) (m:=me) (s:=sb) (s':=sa) (tr:=trb) (tr':=tra) in Hin;
                subst sb; auto
         end
  end.

Ltac low_ins :=
  match goal with
  | [ ce : Reflex.comp _ _, me : msg _ |- _]
      => match goal with
         | [ _ : ValidExchange _ _ _ _ _ _ ce me ?sb ?sa,
             _ : ktr _ _ _ _ ?sa = [?tra]%inhabited,
             Hin : context[inputs _ ?tra] |- _ ]
             => let cs := fresh "cs" in
                let itr := fresh "itr" in
                let trb := fresh "tr" in
                let st := fresh "st" in
                let fd := fresh "fd" in
                destruct sb as [cs itr st fd]_eqn; destruct itr as [trb];
                rewrite ve_inputs_low with (c:=ce) (m:=me) (s:=sb) (s':=sa) (tr:=trb) (tr':=tra) in Hin;
                subst sb; auto
         end
  end.*)