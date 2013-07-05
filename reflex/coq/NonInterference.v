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

Definition vars_eq (s1 s2 : kstate)
  (lblr : fin (projT1 KSTD) -> bool) : bool :=
  shvec_eq _ var_eq _ (kst _ _ _ _ s1) (kst _ _ _ _ s2) lblr.

Definition NonInterferenceSt nd_filt clblr vlblr
  (s1 s2:kstate) : Prop :=
  forall tr1 tr2, ktr _ _ _ _ s1 = [tr1]%inhabited ->
                  ktr _ _ _ _ s2 = [tr2]%inhabited ->
                  call_ok nd_filt tr1 tr2 ->
                  spawn_ok nd_filt tr1 tr2 ->
                  inputs clblr tr1 = inputs clblr tr2 ->
                  outputs clblr tr1 = outputs clblr tr2 /\
                  vars_eq s1 s2 vlblr = true.

Definition NonInterference nd_filt clblr vlblr : Prop :=
  forall s1 s2, Reach s1 -> Reach s2 ->
                NonInterferenceSt nd_filt clblr vlblr s1 s2.

Definition nd_weak : KAction -> bool := fun _ => false.
Definition nd_strong : KAction -> bool := fun _ => true.

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

Lemma vars_eq_sym : forall s1 s2 vlblr,
  vars_eq s1 s2 vlblr = vars_eq s2 s1 vlblr.
Proof.
  intros.
  unfold vars_eq.
  apply shvec_eq_sym.
Qed.

Lemma vars_eq_refl : forall s lblr,
  vars_eq s s lblr = true.
Proof.
  intros. unfold vars_eq. apply shvec_eq_refl.
Qed.

Hint Resolve call_ok_sub spawn_ok_sub call_ok_sym spawn_ok_sym
  vars_eq_sym.

Lemma nist_sym : forall s1 s2 nd_filt clblr vlblr,
  NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
  NonInterferenceSt nd_filt clblr vlblr s2 s1.
Proof.
  intros s1 s2 nd_filt clblr vlblr H.
  unfold NonInterferenceSt in *. intros.
  rewrite vars_eq_sym.
  match goal with
  |- outputs ?clblr ?tr1 = outputs ?clblr ?tr2 /\ ?rest =>
    let Hsym := fresh "Hsym" in
    let Heq := fresh "Heq" in
    cut (outputs clblr tr2 = outputs clblr tr1 /\ rest);
    [ intro Heq; destruct Heq; split; [symmetry; auto | auto]
    | apply H; auto]
  end.
Qed.

Lemma init_st_same : forall s1 s2,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s1 ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT s2 ->
  s1 = s2.
Proof.
  intros s1 s2 HI1 HI2.
  destruct HI1 as [s1' Hs1'].
  destruct HI2 as [s2' Hs2'].
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
  vars_eq s1 s2 lblr = true.
Proof.
  intros s1 s2 lblr HI1 HI2.
  assert (s1 = s2) as Heq by (apply init_st_same; auto).
  subst s1. unfold vars_eq. apply shvec_eq_refl.
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

Ltac spawn_call :=
      match goal with
      | [ Hcall : call_ok _ _ _ |- call_ok _ _ _ ]
          => repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym in Hcall; try assumption;
             repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym; try assumption
      | [ Hspawn : spawn_ok _ _ _ |- spawn_ok _ _ _ ]
          => repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym in Hspawn; try assumption;
             repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym; try assumption
      end.

Definition high_ok clblr vlblr nd_filt :=
  forall c m s1 s1' s2 s2',
  clblr c = true ->
  NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s2 s2' ->
  NonInterferenceSt nd_filt clblr vlblr s1' s2'.

Definition low_ok clblr vlblr nd_filt :=
  forall c m s1 s1' s2,
  clblr c = false ->
  NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
  NonInterferenceSt nd_filt clblr vlblr s1' s2.

Lemma vars_eq_kst : forall s1 s1' s2 s2' vlblr,
  kst _ _ _ _ s1 = kst _ _ _ _ s1' ->
  kst _ _ _ _ s2 = kst _ _ _ _ s2' ->
  vars_eq s1 s2 vlblr = vars_eq s1' s2' vlblr.
Proof.
  intros s1 s1' s2 s2' vlblr Hks1 Hks2. unfold vars_eq.
  rewrite Hks1. rewrite Hks2. reflexivity.
Qed.

Theorem ni_bogus : forall clblr vlblr nd_filt c bmsg sb sa,
  low_ok clblr vlblr nd_filt ->
  (forall s, Reach s ->
    NonInterferenceSt nd_filt clblr vlblr s sb) ->
  BogusExchange PAYD COMPT COMPS KSTD c bmsg sb sa ->
  (forall s, Reach s ->
    NonInterferenceSt nd_filt clblr vlblr s sa).
Proof.
  intros clblr vlblr nd_filt c bmsg sb sa Hlow HNI HBE.
  case_eq (clblr c); intros Hlblr s HReach.
    induction HReach.
      unfold NonInterferenceSt. intros.
      assert (inputs clblr tr1 = nil) as Heq by
        (apply init_inputs_nil with (s:=s) (init:=INIT); auto).
      inversion HBE. subst sa. simpl in *.
      apply pack_injective in H1. subst tr2.
      rewrite Heq in *. simpl in *.
      rewrite Hlblr in *. discriminate.

      case_eq (clblr c0); intro Hlblr'.
        unfold NonInterferenceSt. intros.
        high_ins. inversion HBE. subst sa. simpl in *.
        apply pack_injective in H1. subst tr2.
        simpl in *. rewrite Hlblr in *. discriminate.

        unfold low_ok in Hlow.
        apply Hlow with (c:=c0) (m:=m) (s1:=s); auto.
      
      inversion H; inversion HBE.
      unfold NonInterferenceSt in *. intros. simpl in *.
      apply pack_injective in H6; apply pack_injective in H7.
      subst tr1; rewrite <- H7 in *. simpl in *.
      rewrite Hlblr in *.
      destruct (clblr c0).
        inversion H10.
        split.
          eapply HNI; eauto; try spawn_call.

          pose proof (HNI s HReach tr tr0 H0 H3).
          assert (vars_eq s sb vlblr = true).
            apply H6; auto; try spawn_call.
          rewrite <- H14.
          apply vars_eq_kst; auto.

        split.
          assert (outputs clblr tr0 = outputs clblr tr2).
            rewrite <- H7; auto.
          rewrite H6. rewrite H7 in *.
          eapply IHHReach; eauto; try spawn_call.
          apply f_equal with (f:=ktr _ _ _ _) in H5.
          auto. rewrite <- H7. simpl in *. rewrite Hlblr.
          auto.

          rewrite H5.
          cut (vars_eq s sa vlblr = true).
            intro Hvars. rewrite <- Hvars.
            apply vars_eq_kst; auto.
            eapply IHHReach; eauto; try spawn_call.
            apply f_equal with (f:=ktr _ _ _ _) in H5.
            simpl in *. auto. simpl in *. rewrite Hlblr.
            auto.

    
    unfold NonInterferenceSt in *. intros.
    inversion HBE. subst sa. simpl in *.
    apply pack_injective in H0. subst tr2.
    simpl in *. rewrite Hlblr in *.
    apply HNI; auto; try spawn_call.      
Qed.

Theorem ni_init : forall clblr vlblr nd_filt sinit,
  low_ok clblr vlblr nd_filt ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT sinit ->
  forall s, Reach s -> NonInterferenceSt nd_filt clblr vlblr sinit s.
Proof.
  intros clblr vlblr nd_filt sinit Hlow Hinit s HReach.
  induction HReach.
    unfold NonInterferenceSt; intros.
      assert (tr1 = tr2) as Heq by
        (apply init_tr_same with (s1:=sinit) (s2:=s); auto).
      rewrite Heq.
      split.
        reflexivity.

        apply init_vars_eq; auto.

      case_eq (clblr c); intros.
        unfold NonInterferenceSt.
        intros.
        assert (inputs clblr tr1 = nil) as Heq by
          (apply init_inputs_nil with (s:=sinit) (init:=INIT); auto).
        rewrite Heq in *.
        high_ins.
        discriminate.

        apply nist_sym.
        apply nist_sym in IHHReach.
        unfold low_ok in Hlow.
        apply Hlow with (c:=c) (m:=m) (s1:=s); auto.

      match goal with
      | [ Hbogus : BogusExchange _ _ _ _ _ _ _ _ |- _ ]
        => inversion Hbogus
      end.
      unfold NonInterferenceSt.
      simpl.
      intros.
      match goal with
      | [ Hpacked : [_]%inhabited = [?trpacked]%inhabited |- _ ]
        => apply pack_injective in Hpacked; subst trpacked
      end.
      simpl in *.
      unfold NonInterferenceSt in IHHReach.
      simpl in IHHReach.
      destruct (clblr c).
        assert (inputs clblr tr1 = nil) as Heq by
          (apply init_inputs_nil with (s:=sinit) (init:=INIT); auto).
        rewrite Heq in *.
        discriminate.
      
        apply IHHReach; auto; try spawn_call.
Qed.
  
Theorem ni_suf : forall clblr vlblr nd_filt,
  (forall c m s1 s1' s2 s2',
   clblr c = true ->
   NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
   ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
   ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s2 s2' ->
   NonInterferenceSt nd_filt clblr vlblr s1' s2') ->
  (forall c m s1 s1' s2,
   clblr c = false ->
   NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
   ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
   NonInterferenceSt nd_filt clblr vlblr s1' s2) ->
  NonInterference nd_filt clblr vlblr.
Proof.
  unfold NonInterference.
  intros.
  generalize dependent s2.
  induction H1; intros.
    apply ni_init; auto.

    case_eq (clblr c); intros.    
      induction H3.
        unfold NonInterferenceSt; intros.
        assert (inputs clblr tr2 = nil) as Heq by
          (apply init_inputs_nil with (s:=s0) (init:=INIT); auto).
        rewrite Heq in H9.
        high_ins.
        discriminate.

        case_eq (clblr c0); intros.
          unfold NonInterferenceSt; intros.
          assert (c0 = c) by (repeat high_ins; inversion H11; auto).
          assert (m0 = m) by (repeat high_ins; inversion H11; auto).
          subst c0.
          subst m0.
          unfold NonInterferenceSt at 2 in H.
          apply H with (m:=m) (c:=c) (s1:=s) (s1':=s') (s2:=s0)
            (s2':=s'0); auto.

          apply nist_sym.
          apply nist_sym in IHReach0.
          apply H0 with (c:=c0) (m:=m0) (s1:=s0) (s1':=s'0) (s2:=s');
            auto.
          
        match goal with
        | [ Hbogus : BogusExchange _ _ _ _ _ _ _ _ |- _ ]
          => inversion Hbogus
        end.
        unfold NonInterferenceSt.
        simpl.
        intros.
        match goal with
        | [ Hpacked : [_]%inhabited = [?trpacked]%inhabited |- _ ]
          => apply pack_injective in Hpacked; subst trpacked
        end.
        simpl in *.
        unfold NonInterferenceSt in IHReach.
        simpl in IHReach.
        unfold NonInterferenceSt in IHReach0.
        destruct (clblr c0).
          high_ins.
          discriminate.

          apply IHReach0; auto; try spawn_call.
          
      apply H0 with (c:=c) (m:=m) (s1:=s); auto.

    apply nist_sym.
    apply ni_bogus with (c:=c) (bmsg:=bmsg) (sb:=s) (sa:=s'); auto.
      intros. apply nist_sym. apply IHReach; auto.
Qed.

End NI.