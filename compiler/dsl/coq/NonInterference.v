Require Import Reflex.
Require Import ReflexBase.
Require Import List.
Require Import Ynot.

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

Definition call_ok nd_filt (tr1 : KTrace) (tr2 : KTrace) :=
  forall prog args f1 f2 tr1bef tr1aft tr2bef tr2aft,
    tr1 = tr1aft ++ (KCall prog args f1::tr1bef) ->
    tr2 = tr2aft ++ (KCall prog args f2::tr2bef) ->
    filter nd_filt tr1bef = filter nd_filt tr2bef ->
    f1 = f2.

Definition spawn_ok nd_filt (tr1 : KTrace) (tr2 : KTrace) :=
  forall prog args c1 c2 tr1bef tr1aft tr2bef tr2aft,
    tr1 = tr1aft ++ (KExec prog args c1::tr1bef) ->
    tr2 = tr2aft ++ (KExec prog args c2::tr2bef) ->
    filter nd_filt tr1bef = filter nd_filt tr2bef ->
    (comp_fd _ _ c1) = (comp_fd _ _ c2).

Definition NonInterferenceSt' nd_filt labeler (s1 s2:kstate) : Prop :=
  forall tr1 tr2, ktr _ _ _ _ s1 = [tr1]%inhabited ->
                  ktr _ _ _ _ s2 = [tr2]%inhabited ->
                  call_ok nd_filt tr1 tr2 ->
                  spawn_ok nd_filt tr1 tr2 ->
                  inputs labeler tr1 = inputs labeler tr2 ->
                  outputs labeler tr1 = outputs labeler tr2.

Definition NonInterference' nd_filt labeler : Prop :=
  forall s1 s2, Reach s1 -> Reach s2 ->
                NonInterferenceSt' nd_filt labeler s1 s2.

Definition NonInterference nd_filt labeler : Prop :=
  forall s1 s2 tr1 tr2, Reach s1 -> Reach s2 ->
                        ktr _ _ _ _ s1 = [tr1]%inhabited ->
                        ktr _ _ _ _ s2 = [tr2]%inhabited ->
                        call_ok nd_filt tr1 tr2 ->
                        spawn_ok nd_filt tr1 tr2 ->
                        inputs labeler tr1 = inputs labeler tr2 ->
                        outputs labeler tr1 = outputs labeler tr2.

Definition nd_weak : KAction -> bool := fun _ => false.

(*Non deterministic calls are independent of the trace history.*)
Definition NIWeak := NonInterference nd_weak.
Definition NIWeak' := NonInterference' nd_weak.

Lemma call_ok_sub : forall nd_filt act tr1 tr2,
  call_ok nd_filt tr1 (act::tr2) ->
  call_ok nd_filt tr1 tr2.
Proof.
  unfold call_ok; intros.
  apply H with (prog:=prog) (args:=args) (tr1bef:=tr1bef) (tr2bef:=tr2bef)
               (tr1aft:=tr1aft) (tr2aft:=(act::tr2aft)); subst tr2; auto.
Qed.

Lemma spawn_ok_sub : forall nd_filt act tr1 tr2,
  spawn_ok nd_filt tr1 (act::tr2) ->
  spawn_ok nd_filt tr1 tr2.
Proof.
  unfold spawn_ok; intros.
  apply H with (prog:=prog) (args:=args) (tr1bef:=tr1bef) (tr2bef:=tr2bef)
               (tr1aft:=tr1aft) (tr2aft:=(act::tr2aft)); subst tr2; auto.
Qed.

Lemma call_ok_sym : forall nd_filt tr1 tr2,
  call_ok nd_filt tr1 tr2 ->
  call_ok nd_filt tr2 tr1.
Proof.
  unfold call_ok; intros.
  symmetry.
  eauto.
Qed.

Lemma spawn_ok_sym : forall nd_filt tr1 tr2,
  spawn_ok nd_filt tr1 tr2 ->
  spawn_ok nd_filt tr2 tr1.
Proof.
  unfold spawn_ok; intros.
  symmetry.
  eauto.
Qed.

Hint Resolve call_ok_sub spawn_ok_sub call_ok_sym spawn_ok_sym.

Lemma nist_sym : forall s1 s2 nd_filt lblr,
  NonInterferenceSt' nd_filt lblr s1 s2 ->
  NonInterferenceSt' nd_filt lblr s2 s1.
Proof.
  unfold NonInterferenceSt'.
  intros.
  symmetry.
  apply H; auto.
Qed.

Lemma init_tr_same : forall s1 s2 tr1 tr2,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s1 ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s2 ->
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  tr1 = tr2.
Proof.
  intros s1 s2 tr1 tr2 HI1 HI2 Htr1 Htr2.
  destruct HI1 as [ s1' Hs1' _].
  destruct HI2 as [s2' Hs2' _].
  subst s1'.
  subst s2'.
  apply pack_injective.
  rewrite <- Htr1.
  rewrite <- Htr2.
  reflexivity.
Qed.

Lemma init_inputs_nil : forall s tr lblr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s ->
  ktr _ _ _ _ s = [tr]%inhabited ->
  inputs lblr tr = nil.
Proof.
  intros s tr lblr HInit Htr;
  destruct HInit; subst s;
  generalize dependent tr.
  case_eq (init_ktr _ _ _ _ _ (initial_init_state PAYD COMPT COMPS KSTD IENVD)).
  intros k Htri.
  assert (inputs lblr k = nil) by
      (simpl in Htri; apply pack_injective in Htri; rewrite <- Htri; auto).
  generalize dependent k.
  generalize dependent (initial_init_state PAYD COMPT COMPS KSTD IENVD).
  induction INIT; intros ist k Htri H tr Htr; simpl in *;
    try (destruct ist; destruct init_ktr as [k']; simpl in *;
    apply pack_injective in Htr; subst tr; apply pack_injective in Htri;
    subst k'; auto).

    case_eq (init_ktr _ _ _ _ _
               (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD IENVD ist i1));
    intros.
    apply IHi2 with
      (i:=(init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD IENVD ist i1))
      (k:=k0); auto.
    apply IHi1 with (i:=ist) (k:=k); auto.
    destruct ist; auto.

    destruct ist;
    match goal with
    | [ _ : context[if ?e then _ else _] |- _ ]
        => destruct e
    end; eauto.

    (*Send all*)
    induction init_comps; auto; simpl;
      match goal with
      |- context[ if ?e then _ else _ ]
         => destruct e
      end; auto.
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
       pay := eval_hdlr_payload_expr PAYD COMPT COMPS KSTD c m envd kst henv
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
    exists nil.
    split; auto.
    intros.
    simpl in *.
    contradiction.
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
  end.

Theorem ni_suf : forall lblr nd_filt,
  (forall c m s1 s1' s2 s2',
     lblr c = true ->
     NonInterferenceSt' nd_filt lblr s1 s2 ->
     ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
     ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s2 s2' ->
     NonInterferenceSt' nd_filt lblr s1' s2') ->
  (forall c m s1 s1' s2,
     lblr c = false ->
     NonInterferenceSt' nd_filt lblr s1 s2 ->
     ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
     NonInterferenceSt' nd_filt lblr s1' s2) ->
  NonInterference' nd_filt lblr.
Proof.
  unfold NonInterference'.
  intros.
  generalize dependent s2.
  induction H1; intros.
    induction H2.
      unfold NonInterferenceSt'; intros.
      assert (tr1 = tr2) as Heq by (apply init_tr_same with (s1:=s) (s2:=s0); auto).
      rewrite Heq.
      reflexivity.

      case_eq (lblr c); intros.
        unfold NonInterferenceSt'.
        intros.
        assert (inputs lblr tr1 = nil) as Heq by
          (apply init_inputs_nil with (s:=s); auto).
        rewrite Heq in H9.
        high_ins.
        discriminate.

        apply nist_sym.
        apply nist_sym in IHReach.
        apply H0 with (c:=c) (m:=m) (s1:=s0); auto.

      rewrite H4.
      unfold NonInterferenceSt'.
      simpl.
      intros.
      apply pack_injective in H6.
      subst tr2.
      simpl in *.
      unfold NonInterferenceSt' in IHReach.
      simpl in IHReach.
      destruct (lblr f).
        assert (inputs lblr tr1 = nil) as Heq by
          (apply init_inputs_nil with (s:=s); auto).
        rewrite Heq in H9.
        discriminate.
      
        apply IHReach; auto.
          repeat apply call_ok_sub in H7; assumption.
          repeat apply spawn_ok_sub in H8; assumption.

    case_eq (lblr c); intros.    
      induction H3.
        unfold NonInterferenceSt'; intros.
        assert (inputs lblr tr2 = nil) as Heq by
          (apply init_inputs_nil with (s:=s0); auto).
        rewrite Heq in H9.
        high_ins.
        discriminate.

        case_eq (lblr c0); intros.
          unfold NonInterferenceSt'; intros.
          assert (c0 = c) by (repeat high_ins; inversion H11; auto).
          assert (m0 = m) by (repeat high_ins; inversion H11; auto).
          subst c0.
          subst m0.
          unfold NonInterferenceSt' at 2 in H.
          apply H with (m:=m) (c:=c) (s1:=s) (s1':=s') (s2:=s0) (s2':=s'0); auto.

          apply nist_sym.
          apply nist_sym in IHReach0.
          apply H0 with (c:=c0) (m:=m0) (s1:=s0) (s1':=s'0) (s2:=s'); auto.
          
        rewrite H6.
        unfold NonInterferenceSt'.
        simpl.
        intros.
        apply pack_injective in H8.
        subst tr2.
        simpl in *.
        unfold NonInterferenceSt' in IHReach.
        simpl in IHReach.
        unfold NonInterferenceSt' in IHReach0.
        destruct (lblr f).
          high_ins.
          discriminate.

          apply IHReach0; auto.
            repeat apply call_ok_sub in H9; assumption.
            repeat apply spawn_ok_sub in H10; assumption.
          
      apply H0 with (c:=c) (m:=m) (s1:=s); auto.

    rewrite H3.
    unfold NonInterferenceSt'.
    simpl.
    intros.
    apply pack_injective in H5.
    subst tr1.
    simpl in *.
    case_eq (lblr f); intros.
      rewrite H5 in *.
      generalize dependent tr2.
      induction H4; intros.
        assert (inputs lblr tr2 = nil) as Heq by
          (apply init_inputs_nil with (s:=s0); auto).
        rewrite Heq in H9.
        discriminate.

        case_eq (lblr c); intros.
          high_ins.
          discriminate.

          low_ins.
          unfold NonInterferenceSt' in H0.
          symmetry.
          apply H0 with (c:=c) (m:=m) (s1:={| kcs := cs0; ktr := [tr0]; kst := st; kfd := fd |})
                        (s1':=s'0) (s2:=s') (tr1:=tr2)
                        (tr2:=KBogus PAYD COMPT COMPS f bmsg :: KSelect PAYD COMPT COMPS cs f :: tr); auto.
          intros.
          subst s'.
          simpl in *.
          apply pack_injective in H13.
          subst tr3.
          simpl.
          symmetry.
          eapply IHReach0; eauto.
          apply pack_injective in H12.
          subst tr1.
          assumption.
          subst s'; auto.
          simpl.
          rewrite H5 in *.
          symmetry.
          rewrite <- ve_inputs_low with (c:=c) (m:=m) (s:={| kcs := cs0; ktr := [tr0]; kst := st; kfd := fd |})
                                     (s':=s'0) (tr:=tr0) (tr':=tr2) in H10; auto.

          subst s'0.
          simpl in *.
          apply pack_injective in H8.
          subst tr2.
          simpl in *.
          destruct (lblr f0).
            inversion H11.
            unfold NonInterferenceSt' in IHReach.
            eapply IHReach; eauto.
            repeat apply call_ok_sub in H9; apply call_ok_sym in H9;
            repeat apply call_ok_sub in H9; apply call_ok_sym in H9; assumption.
            repeat apply spawn_ok_sub in H10; apply spawn_ok_sym in H10;
            repeat apply spawn_ok_sub in H10; apply spawn_ok_sym in H10; assumption.

            eapply IHReach0; auto.
            repeat apply call_ok_sub in H9. assumption.
            repeat apply spawn_ok_sub in H10; assumption.
          
      rewrite H5 in *.
      unfold NonInterferenceSt' in IHReach.
      simpl in IHReach.
      eapply IHReach; eauto.
Qed.

End NI.