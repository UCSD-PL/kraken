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

Definition mk_filt nd_filt (a:Action) : bool :=
  match a with
  | Exec _ _ _ => nd_filt a
  | Call _ _ _ => nd_filt a
  | _          => false
  end.

Definition filter_trace nd_filt tr :=
  filter (mk_filt nd_filt) tr.

Definition filter_ktrace nd_filt tr :=
  filter_trace nd_filt (expand_ktrace PAYD COMPT COMPS tr).

Definition nd_ok nd_filt := forall d tr,
  oracle d [tr] = oracle d [filter_trace nd_filt tr].

(*
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
*)

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
  (lblr : fin (projT1 KSTD) -> bool) :=  
  shvec_erase _ lblr _ (kst _ _ _ _ s1) = shvec_erase _ lblr _ (kst _ _ _ _ s2).

Definition NonInterferenceSt nd_filt clblr vlblr
  (s1 s2:kstate) : Prop :=
  forall tr1 tr2, ktr _ _ _ _ s1 = [tr1]%inhabited ->
                  ktr _ _ _ _ s2 = [tr2]%inhabited ->
                  nd_ok nd_filt ->
                  inputs clblr tr1 = inputs clblr tr2 ->
                  outputs clblr tr1 = outputs clblr tr2 /\
                  vars_eq s1 s2 vlblr.

Definition NonInterference nd_filt clblr vlblr : Prop :=
  forall s1 s2, Reach s1 -> Reach s2 ->
                NonInterferenceSt nd_filt clblr vlblr s1 s2.

Definition nd_weak : Action -> bool := fun _ => false.
Definition nd_strong : Action -> bool := fun _ => true.

(*
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

Hint Resolve call_ok_sub spawn_ok_sub call_ok_sym spawn_ok_sym.*)

Lemma nist_sym : forall s1 s2 nd_filt clblr vlblr,
  NonInterferenceSt nd_filt clblr vlblr s1 s2 ->
  NonInterferenceSt nd_filt clblr vlblr s2 s1.
Proof.
  intros s1 s2 nd_filt clblr vlblr H.
  unfold NonInterferenceSt in *. intros.
  split.
    symmetry; apply H; auto.

    unfold vars_eq in *. symmetry.
    eapply H; eauto.
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
  end.

(*
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
      end.*)

Lemma vars_eq_kst : forall s1 s1' s2 s2' vlblr,
  kst _ _ _ _ s1 = kst _ _ _ _ s1' ->
  kst _ _ _ _ s2 = kst _ _ _ _ s2' ->
  vars_eq s1 s2 vlblr -> vars_eq s1' s2' vlblr.
Proof.
  intros s1 s1' s2 s2' vlblr Hks1 Hks2 Heq. unfold vars_eq in *.
  rewrite <- Hks1. rewrite <- Hks2. assumption.
Qed.

Ltac uninhabit :=
  match goal with
  | [ H : [?tr1]%inhabited = [?tr2]%inhabited |- _ ]
    => apply pack_injective in H;
       (subst tr1 || subst tr2)
  end.

Ltac unpack_bogus :=
  match goal with
  | [ HBE : BogusExchange _ _ _ _ _ _ _ ?sa |- _ ]
    => inversion HBE;
       match goal with
       | [ H : _ = sa |- _ ]
         => rewrite <- H in *; simpl in *;
            uninhabit; simpl in *
       end
  end.

(*
Lemma call_ok_ve : forall nd_filt c m (s1 s1' s2:kstate) tr1 tr1' tr2,
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s1' = [tr1']%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  call_ok nd_filt tr1' tr2 ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
  call_ok nd_filt tr1 tr2.
Proof.
  unfold call_ok. intros.
  pose proof (ve_tr_sub c m s1 s1' tr1 tr1' H H0 H3).
  destruct H7.
  eapply H2 with (tr1aft:=x++tr1aft); eauto.
  rewrite app_ass.
  rewrite <- H4.
  auto.
Qed.

Lemma call_ok_bogus : forall nd_filt c m (s1 s1' s2:kstate) tr1 tr1' tr2,
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s1' = [tr1']%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  call_ok nd_filt tr1' tr2 ->
  BogusExchange PAYD COMPT COMPS KSTD c m s1 s1' ->
  call_ok nd_filt tr1 tr2.
Proof.
  unfold call_ok. intros.
  unpack_bogus.
  eapply H2 with
    (tr1aft:=KBogus PAYD COMPT COMPS c m :: KSelect PAYD COMPT COMPS cs c :: tr1aft);
    eauto.
  rewrite H7 in H.
  apply pack_injective in H.
  subst tr.
  subst tr1.
  auto.
Qed.

Lemma spawn_ok_ve : forall nd_filt c m (s1 s1' s2:kstate) tr1 tr1' tr2,
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s1' = [tr1']%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  spawn_ok nd_filt tr1' tr2 ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
  spawn_ok nd_filt tr1 tr2.
Proof.
  unfold spawn_ok. intros.
  pose proof (ve_tr_sub c m s1 s1' tr1 tr1' H H0 H3).
  destruct H7.
  eapply H2 with (tr1aft:=x++tr1aft); eauto.
  rewrite app_ass.
  rewrite <- H4.
  auto.
Qed.

Lemma spawn_ok_bogus : forall nd_filt c m (s1 s1' s2:kstate) tr1 tr1' tr2,
  ktr _ _ _ _ s1 = [tr1]%inhabited ->
  ktr _ _ _ _ s1' = [tr1']%inhabited ->
  ktr _ _ _ _ s2 = [tr2]%inhabited ->
  spawn_ok nd_filt tr1' tr2 ->
  BogusExchange PAYD COMPT COMPS KSTD c m s1 s1' ->
  spawn_ok nd_filt tr1 tr2.
Proof.
  unfold spawn_ok. intros.
  unpack_bogus.
  eapply H2 with
    (tr1aft:=KBogus PAYD COMPT COMPS c m :: KSelect PAYD COMPT COMPS cs c :: tr1aft);
    eauto.
  rewrite H7 in H.
  apply pack_injective in H.
  subst tr.
  subst tr1.
  auto.
Qed.*)

Definition low_ok clblr vlblr nd_filt := forall c m s s' tr tr',
  ktr _ _ _ _ s = [tr]%inhabited ->
  ktr _ _ _ _ s' = [tr']%inhabited ->
  clblr c = false ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s s' ->
  outputs clblr tr = outputs clblr tr' /\
  vars_eq s s' vlblr /\
  filter_ktrace nd_filt tr = filter_ktrace nd_filt tr'.

Definition high_ok clblr vlblr nd_filt :=
  forall c m s1 s1' s2 s2' tr1 tr1' tr2 tr2',
    clblr c = true ->
    ktr _ _ _ _ s1 = [tr1]%inhabited ->
    ktr _ _ _ _ s1' = [tr1']%inhabited ->
    ktr _ _ _ _ s2 = [tr2]%inhabited ->
    ktr _ _ _ _ s2' = [tr2']%inhabited ->
    outputs clblr tr1 = outputs clblr tr2 ->
    vars_eq s1 s2 vlblr ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s1 s1' ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m s2 s2' ->
    nd_ok nd_filt ->
    filter_ktrace nd_filt tr1 = filter_ktrace nd_filt tr2 ->
    outputs clblr tr1' = outputs clblr tr2' /\ vars_eq s1' s2' vlblr
    /\ filter_ktrace nd_filt tr1' = filter_ktrace nd_filt tr2'.

Definition NonInterferenceSt' nd_filt clblr vlblr
  (s1 s2:kstate) : Prop :=
  forall tr1 tr2, ktr _ _ _ _ s1 = [tr1]%inhabited ->
                  ktr _ _ _ _ s2 = [tr2]%inhabited ->
                  nd_ok nd_filt ->
                  inputs clblr tr1 = inputs clblr tr2 ->
                  outputs clblr tr1 = outputs clblr tr2 /\
                  vars_eq s1 s2 vlblr /\
                  filter_ktrace nd_filt tr1 =
                  filter_ktrace nd_filt tr2.

Definition NonInterference' nd_filt clblr vlblr : Prop :=
  forall s1 s2, Reach s1 -> Reach s2 ->
                NonInterferenceSt' nd_filt clblr vlblr s1 s2.

Lemma nist_sym' : forall s1 s2 nd_filt clblr vlblr,
  NonInterferenceSt' nd_filt clblr vlblr s1 s2 ->
  NonInterferenceSt' nd_filt clblr vlblr s2 s1.
Proof.
  intros s1 s2 nd_filt clblr vlblr H.
  unfold NonInterferenceSt' in *. intros.
  split.
    symmetry; apply H; auto.

    split.
      unfold vars_eq in *. symmetry.
      eapply H; eauto.
    
      symmetry; eapply H; eauto.
Qed.

Lemma low_ok_ve : forall clblr vlblr nd_filt c m sb sa,
  low_ok clblr vlblr nd_filt ->
  clblr c = false ->
  (forall s : Reflex.kstate PAYD COMPT COMPS KSTD,
    Reach s -> NonInterferenceSt' nd_filt clblr vlblr sb s) ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m sb sa ->
  (forall s, Reach s ->
    NonInterferenceSt' nd_filt clblr vlblr sa s).
Proof.
  intros clblr vlblr nd_filt c m sb sa Hlow Hlblr HNI Hve s HReach.
    unfold low_ok in Hlow.
    unfold NonInterferenceSt'; intros.
    assert (vars_eq sb sa vlblr) as Hvars_eq.
      destruct sb; destruct ktr; eapply Hlow; eauto.
    destruct sb as [css ktrs sts fds]_eqn; destruct ktrs as [trs].
    assert (outputs clblr trs = outputs clblr tr1) as Houts_eq.
      eapply Hlow; eauto. simpl. auto.
    assert (filter_ktrace nd_filt trs =
      filter_ktrace nd_filt tr1) as Hfilt_eq.
      eapply Hlow; eauto. simpl. auto.
    unfold vars_eq in *.
    rewrite <- Hvars_eq.
    rewrite <- Houts_eq.
    rewrite <- Hfilt_eq.
    eapply HNI; eauto.
    match goal with
    | [ Hin : inputs _ _ = _ |- _ ]
      => erewrite ve_inputs_low in Hin; eauto
    end. simpl. auto.
Qed.

Lemma bogus_filt : forall nd_filt c bmsg s s' tr tr',
  ktr _ _ _ _ s = [tr]%inhabited ->
  ktr _ _ _ _ s' = [tr']%inhabited ->
  BogusExchange PAYD COMPT COMPS KSTD c bmsg s s' ->
  filter_ktrace nd_filt tr =
  filter_ktrace nd_filt tr'.
Proof.
  intros.
  unpack_bogus.
  unfold filter_ktrace in *.
  simpl in *.
  unfold trace_recv_bogus_msg in *.
  destruct (btag bmsg).
  assert (RecvNum (comp_fd COMPT COMPS c) (Num a a0) =
    Recv (comp_fd COMPT COMPS c) (a0::a::nil)::nil) as Heq.
    auto.
  rewrite Heq in *.
  simpl in *.
  rewrite H2 in H.
  apply pack_injective in H.
  subst tr.
  reflexivity.
Qed.

Theorem ni_bogus : forall clblr vlblr nd_filt c bmsg sb sa,
  low_ok clblr vlblr nd_filt ->
  (forall s, Reach s ->
    NonInterferenceSt' nd_filt clblr vlblr s sb) ->
  BogusExchange PAYD COMPT COMPS KSTD c bmsg sb sa ->
  (forall s, Reach s ->
    NonInterferenceSt' nd_filt clblr vlblr s sa).
Proof.
  intros clblr vlblr nd_filt c bmsg sb sa Hlow HNI HBE s HReach.
  unfold NonInterferenceSt'. intros.
  unpack_bogus.
  erewrite <- bogus_filt with (s:=sb) (s':=sa)
    (tr:=tr) (tr':=KBogus PAYD COMPT COMPS c bmsg
      :: KSelect PAYD COMPT COMPS cs c :: tr) (c:=c)
    (bmsg:=bmsg); eauto;
      try solve [apply f_equal with (f:=ktr _ _ _ _) in H5;
        simpl in H5; auto | subst sa; auto].
  destruct (clblr c).
    generalize dependent tr1.
    induction HReach; intros.
      match goal with
      | [ Hin : inputs _ _ = _ |- _ ]
        => erewrite init_inputs_nil in Hin; eauto
      end.
      discriminate.

      case_eq (clblr c0); intros.
        high_ins. discriminate.

        assert (vars_eq s s' vlblr) as Hvars_eq.
          destruct s; destruct ktr; eapply Hlow; eauto.
        destruct s as [css ktrs sts fds]_eqn; destruct ktrs as [trs].
        assert (outputs clblr trs = outputs clblr tr1) as Houts_eq.
          eapply Hlow; eauto. simpl. auto.
        assert (filter_ktrace nd_filt trs =
          filter_ktrace nd_filt tr1) as Hfilt_eq.
          eapply Hlow; eauto. simpl. auto.
        unfold vars_eq in *.
        rewrite <- Hvars_eq.
        rewrite <- Houts_eq.
        rewrite <- Hfilt_eq.
        eapply IHHReach; eauto.
        subst sa; simpl; auto.
        match goal with
        | [ Hin : inputs _ _ = _ |- _ ]
          => erewrite ve_inputs_low in Hin; eauto
        end. simpl. auto.
      
      unpack_bogus.
      destruct (clblr c0).
        match goal with
        | [ Hin : context[inputs _ _] |- _ ]
          => inversion Hin
        end.
        inversion H3.
        unfold NonInterferenceSt' in HNI.
        unfold vars_eq in *.
        simpl in *.
        unfold filter_ktrace in *.
        simpl in *.
        unfold trace_recv_bogus_msg.
        destruct (btag bmsg).
        assert (RecvNum (comp_fd COMPT COMPS c) (Num a a0) =
           Recv (comp_fd COMPT COMPS c) (a0::a::nil)::nil) as Heq'.
           auto.
        rewrite Heq'. simpl.
        eapply HNI; eauto.

        unfold filter_ktrace in *.
        simpl in *.
        unfold trace_recv_bogus_msg in *.
        destruct (btag bmsg0).
        assert (RecvNum (comp_fd COMPT COMPS c0) (Num a a0) =
           Recv (comp_fd COMPT COMPS c0) (a0::a::nil)::nil) as Heq'.
           auto.
        rewrite Heq' in *.
        simpl in *.
        eapply IHHReach; eauto.

    unfold NonInterferenceSt' in *.
    unfold vars_eq in *.
    simpl in *.
    eapply HNI; eauto.
Qed.

Theorem ni_init : forall clblr vlblr nd_filt sinit,
  low_ok clblr vlblr nd_filt ->
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT sinit ->
  forall s, Reach s -> NonInterferenceSt' nd_filt clblr vlblr sinit s.
Proof.
  intros clblr vlblr nd_filt sinit Hlow Hinit s HReach.
  induction HReach; intros.
    unfold NonInterferenceSt'. intros.
    erewrite init_tr_same with (tr1:=tr1)
        (tr2:=tr2) (s1:=sinit); eauto.
    split;
      split.
        apply init_vars_eq; auto.

        reflexivity.

    case_eq (clblr c); intros.
      unfold NonInterferenceSt'. intros.
      match goal with
      | [ Hin : inputs _ _ = _ |- _ ]
        => erewrite init_inputs_nil in Hin; eauto
      end.
      high_ins. discriminate.

      apply nist_sym'.
      apply nist_sym' in IHHReach.
      unfold low_ok in Hlow.
      unfold NonInterferenceSt' in *. intros.
      assert (vars_eq s s' vlblr) as Hvars_eq.
        destruct s; destruct ktr; eapply Hlow; eauto.
      destruct s as [css ktrs sts fds]_eqn; destruct ktrs as [trs].
      assert (outputs clblr trs = outputs clblr tr1) as Houts_eq.
        eapply Hlow; eauto. simpl. auto.
      assert (filter_ktrace nd_filt trs =
        filter_ktrace nd_filt tr1) as Hfilt_eq.
        eapply Hlow; eauto; simpl; auto.
      unfold vars_eq in *.
      rewrite <- Hvars_eq.
      rewrite <- Houts_eq.
      rewrite <- Hfilt_eq.
      eapply IHHReach; eauto.
      match goal with
      | [ Hin : inputs _ _ = _ |- _ ]
        => erewrite ve_inputs_low in Hin; eauto
      end. simpl. auto.

      match goal with
      | [ Hbogus : BogusExchange _ _ _ _ _ _ _ _ |- _ ]
        => inversion Hbogus
      end.
      unfold NonInterferenceSt.
      split; intros;
      simpl in *;
      match goal with
      | [ Hpacked : [_]%inhabited = [?trpacked]%inhabited |- _ ]
        => apply pack_injective in Hpacked; subst trpacked
      end;
      simpl in *;
      unfold NonInterferenceSt in IHHReach;
      destruct (clblr c);
        try (assert (inputs clblr tr1 = nil) as Heq by
          (apply init_inputs_nil with (s:=sinit) (init:=INIT); auto);
        rewrite Heq in *;
        discriminate).
      
        apply IHHReach; auto.
        split.
          unfold vars_eq in *. simpl. 
          eapply IHHReach; eauto.

          erewrite <- bogus_filt with (s:=s) (s':=s')
            (tr:=tr) (tr':=KBogus PAYD COMPT COMPS c bmsg ::
              KSelect PAYD COMPT COMPS cs c :: tr); eauto.
          eapply IHHReach; eauto.
          apply f_equal with (f:=ktr _ _ _ _) in H2; eauto.
Qed.

(*Lemma high_low_nd :
  forall clblr vlblr nd_filt (s1 s2:kstate) tr1 tr2,
    high_ok clblr vlblr nd_filt ->
    low_ok clblr vlblr nd_filt ->
    ktr _ _ _ _ s1 = [tr1]%inhabited ->
    ktr _ _ _ _ s2 = [tr2]%inhabited ->
    Reach s1 -> Reach s2 ->
    inputs clblr tr1 = inputs clblr tr2 ->
    outputs clblr tr1 = outputs clblr tr2 ->
    vars_eq s1 s2 vlblr ->
    filter_ktrace nd_filt tr1 = filter_ktrace nd_filt tr2.
Proof.
  intros clblr vlblr nd_filt s1 s2 tr1 tr2 Hhigh Hlow
    Hktr1 Hktr2 HReach1 HReach2 Hin.
  generalize dependent s2.
  generalize dependent tr1.
  induction HReach1; intros tr1 Hktr1 Hin s2 Hktr2 HReach2.
    generalize dependent tr2.
    induction HReach2; intros.
      erewrite <- init_tr_same with (tr1:=tr1) (tr2:=tr2)
        (s1:=s) (s2:=s0); eauto.

       case_eq (clblr c); intros.
         unfold NonInterferenceSt. intros.
         match goal with
         | [ Hin : inputs _ _ = _ |- _ ]
           => erewrite init_inputs_nil in Hin; eauto
         end.
         high_ins. discriminate.

         symmetry. symmetry in IHHReach2. low_ins.
         assert (filter_ktrace nd_filt tr =
           filter_ktrace nd_filt tr2) as Heq.
           eapply Hlow with
             (s:={| kcs := cs; ktr := [tr]; kst := st; kfd := fd |})
             (s':=s'); eauto.
         assert (outputs clblr tr = outputs clblr tr2) as Heq_out.
           eapply Hlow with
             (s:={| kcs := cs; ktr := [tr]; kst := st; kfd := fd |})
             (s':=s') (tr:=tr) (tr':=tr2); eauto.
         assert (vars_eq 
           {| kcs := cs; ktr := [tr]; kst := st; kfd := fd |} s'
           vlblr) as Heq_vars.
           eapply Hlow with
             (s:={| kcs := cs; ktr := [tr]; kst := st; kfd := fd |})
             (s':=s') (tr:=tr) (tr':=tr2); eauto.
         rewrite <- Heq.
         eapply IHHReach2; eauto.
         rewrite Heq_out; auto.
         unfold vars_eq in *.
         rewrite Heq_vars; auto.

       unpack_bogus.
       destruct (clblr c).
         erewrite init_inputs_nil in Hin; eauto.
         discriminate.
      
         unfold filter_ktrace.
         simpl.
         unfold trace_recv_bogus_msg.
         destruct (btag bmsg).
         assert (RecvNum (comp_fd COMPT COMPS c) (Num a a0) =
           Recv (comp_fd COMPT COMPS c) (a0::a::nil)::nil) as Heq.
           auto.
         rewrite Heq.
         simpl.
         eapply IHHReach2; auto.

      case_eq (clblr c); intros.
        generalize dependent tr2.
        induction HReach2; intros.
          erewrite init_inputs_nil with (s:=s0) (tr:=tr2)
            in Hin; eauto.
          destruct s. destruct ktr.
          erewrite ve_inputs_high with
            (s:={| kcs := kcs; ktr := [k]; kst := kst; kfd := kfd |})
            (s':=s') (tr:=k) (tr':=tr1) in Hin; eauto.
          discriminate.

          case_eq (clblr c0); intros.
            repeat high_ins. inversion Hin.
            subst c0; subst m0.
            eapply Hhigh with (s1':=s') (s2':=s'0)
              (s1:={| kcs := cs0; ktr := [tr0];
                kst := st0; kfd := fd0 |})
              (s2:={| kcs := cs; ktr := [tr];
                kst := st; kfd := fd |}); eauto.
Admitted.            
          *)  

Theorem ni_ve :  forall clblr vlblr nd_filt c m sb sa,
  high_ok clblr vlblr nd_filt ->
  low_ok clblr vlblr nd_filt ->
  (forall s, Reach s ->
    NonInterferenceSt' nd_filt clblr vlblr sb s) ->
  Reach sb ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m sb sa ->
  (forall s, Reach s ->
    NonInterferenceSt' nd_filt clblr vlblr sa s).
Proof.
  intros clblr vlblr nd_filt c m sb sa Hhigh Hlow HNI HReachb Hve s HReach.
  case_eq (clblr c); intro Hlblr.
    induction HReach.
      apply nist_sym'; eapply ni_init; eauto.
      eapply Reach_valid; eauto.

      case_eq (clblr c0); intros.
        unfold NonInterferenceSt'. intros.
        repeat high_ins. simpl. 
        match goal with
        | [ Hin : context[inputs _ _] |- _ ]
          => inversion Hin
        end. subst c; subst m.
        unfold high_ok in Hhigh.
        split;
        eapply Hhigh with (s1':=sa) (s2':=s')
          (s1:={| kcs := cs0; ktr := [tr0]; kst := st0; kfd := fd0 |})
          (s2:={| kcs := cs; ktr := [tr]; kst := st; kfd := fd |})
          (tr1':=tr1) (tr2':=tr2);
          eauto;
        try (eapply HNI; eauto).
(*        eapply high_low_nd with
          (s1:={| kcs := cs0; ktr := [tr0]; kst := st0; kfd := fd0 |})
          (s2:={| kcs := cs; ktr := [tr]; kst := st; kfd := fd |});
          eauto.*)

        apply nist_sym'; apply nist_sym' in IHHReach.
        unfold low_ok in Hlow.
        unfold NonInterferenceSt'. intros.
        assert (vars_eq s s' vlblr) as Hvars_eq.
          destruct s; destruct ktr; eapply Hlow; eauto.
        destruct s as [css ktrs sts fds]_eqn; destruct ktrs as [trs].
        assert (outputs clblr trs = outputs clblr tr1) as Houts_eq.
          eapply Hlow; eauto. simpl. auto.
        assert (filter_ktrace nd_filt trs =
          filter_ktrace nd_filt tr1) as Hfilt_eq.
          eapply Hlow; eauto. simpl. auto.
        unfold vars_eq in *.
        rewrite <- Hvars_eq.
        rewrite <- Houts_eq.
        rewrite <- Hfilt_eq.
        eapply IHHReach; eauto.
        match goal with
        | [ Hin : inputs _ _ = _ |- _ ]
          => erewrite ve_inputs_low in Hin; eauto
        end. simpl. auto.

      match goal with
      | [ Hbogus : BogusExchange _ _ _ _ _ _ _ _ |- _ ]
        => inversion Hbogus
      end.
      unfold NonInterferenceSt'. intros. simpl in *.
      match goal with
      | [ Hpacked : [_]%inhabited = [?trpacked]%inhabited |- _ ]
        => apply pack_injective in Hpacked; subst trpacked
      end. simpl in *.
      destruct (clblr c0).
        high_ins; discriminate.

        erewrite <- bogus_filt with (s:=s) (s':=s')
            (tr:=tr) (tr':=KBogus PAYD COMPT COMPS c0 bmsg ::
              KSelect PAYD COMPT COMPS cs c0 :: tr); eauto.
        apply f_equal with (f:=ktr _ _ _ _) in H2; eauto.

    eapply low_ok_ve; eauto.
Qed.

Theorem ni_suf' : forall clblr vlblr nd_filt,
  high_ok clblr vlblr nd_filt ->
  low_ok clblr vlblr nd_filt ->
  NonInterference' nd_filt clblr vlblr.
Proof.
  intros clblr vlblr nd_filt Hlow Hhigh.
  unfold NonInterference'. intros s1 s2 HReach1 HReach2.
  generalize dependent s2.
  induction HReach1; intros s2 HReach2.
    apply ni_init; auto.

    eapply ni_ve; eauto.

    apply nist_sym'; eapply ni_bogus; eauto.
    intros. apply nist_sym'; auto.
Qed.

Theorem nist'_nist : forall clblr vlblr nd_filt s s',
  NonInterferenceSt' clblr vlblr nd_filt s s' ->
  NonInterferenceSt clblr vlblr nd_filt s s'.
Proof.
  intros.
  unfold NonInterferenceSt.
  unfold NonInterferenceSt' in *.
  intros.
  pose proof (H tr1 tr2 H0 H1 H2 H3).
  destruct H4.
  destruct H5.
  auto.
Qed.

Theorem ni'_ni : forall clblr vlblr nd_filt,
  NonInterference' nd_filt clblr vlblr ->
  NonInterference nd_filt clblr vlblr.
Proof.
  intros.
  unfold NonInterference.
  unfold NonInterference' in *.
  intros.
  pose proof (H s1 s2 H0 H1).
  apply nist'_nist; auto.
Qed.

Theorem ni_suf : forall clblr vlblr nd_filt,
  high_ok clblr vlblr nd_filt ->
  low_ok clblr vlblr nd_filt ->
  NonInterference nd_filt clblr vlblr.
Proof.
  intros.
  apply ni'_ni.
  apply ni_suf'; auto.
Qed.

End NI.