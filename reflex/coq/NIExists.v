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
Definition kcs := kcs PAYD COMPT COMPS KSTD.

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

Definition cs_eq (s1 s2 : kstate) cslblr :=
  filter cslblr (kcs s1) = filter cslblr (kcs s2).

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

Definition NI clblr vlblr cslblr := forall s,
  Reach s ->
  (exists snil,
    Reach snil /\
    high_in_eq s snil clblr /\
    low_in_nil snil clblr /\
    high_out_eq s snil clblr /\
    vars_eq s snil vlblr /\
    cs_eq s snil cslblr).

Definition low_ok clblr vlblr cslblr := forall c m i s s',
  clblr c = false ->
  Reach s ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s s' ->
  high_out_eq s s' clblr /\
  vars_eq s s' vlblr /\
  cs_eq s s' cslblr.

Definition high_ok clblr vlblr cslblr :=
  forall c m i s1 s1' s2 s2',
    clblr c = true ->
    high_out_eq s1 s2 clblr ->
    vars_eq s1 s2 vlblr ->
    cs_eq s1 s2 cslblr ->
    Reach s1 -> Reach s2 ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s1 s1' ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s2 s2' ->
    high_out_eq s1' s2' clblr /\ vars_eq s1' s2' vlblr /\
    cs_eq s1' s2' cslblr.

Ltac uninhabit :=
  match goal with
  | [ H : [_]%inhabited = [?tr]%inhabited |- _ ]
    => apply pack_injective in H; subst tr
  end.

Definition high_comp_pat COMPT COMPTDEC COMPS cp clblr :=
  forall c, match_comp COMPT COMPTDEC COMPS cp c = true ->
    clblr c = true.

Definition exec_comps (a : KAction) (l : list comp) : list comp :=
  match a with
  | Reflex.KExec _ _ c => c::l
  | _           => l
  end.

Lemma hout_init' : forall clblr envd s cmd input tr tr',
  init_ktr _ _ _ _ _ s = [tr]%inhabited ->
  filter clblr (init_comps _ _ _ _ _ s) = fold_right exec_comps nil (outputs clblr tr) ->
  let s' := init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd s cmd input in
  init_ktr _ _ _ _ _ s' = [tr']%inhabited ->
  filter clblr (init_comps _ _ _ _ _ s') = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr envd s cmd input tr tr' Htr Heq s' Htr'. subst s'.
  generalize dependent s. generalize dependent tr. generalize dependent tr'.
  induction cmd; simpl; intros tr' tr s Htr Heq Htr'.
    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd s cmd1
              (fst input)) as [? [itr] ? ?]_eqn.
    apply IHcmd2 with (tr:=itr); auto.
    rewrite <- Heqi.
    apply IHcmd1 with (tr:=tr); auto.
    rewrite Heqi. auto.

    destruct (num_eq
              (eval_base_expr COMPT COMPS
                 (init_env PAYD COMPT COMPS KSTD envd s) e) FALSE).
      apply IHcmd2 with (tr:=tr); auto.
      apply IHcmd1 with (tr:=tr); auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl.
    destruct (clblr
           (projT1
              (eval_base_expr COMPT COMPS
                 (init_env PAYD COMPT COMPS KSTD envd s) e))); auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl.
    destruct (clblr
         {|
         comp_type := t;
         comp_fd := input;
         comp_conf := eval_base_payload_expr COMPT COMPS envd
                        (init_env PAYD COMPT COMPS KSTD envd s)
                        (comp_conf_desc COMPT COMPS t) p |}); auto.
    simpl. f_equal. auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl. auto.

    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (find_comp COMPT COMPTDEC COMPS
               (eval_base_comp_pat COMPT COMPS envd
                  (init_env PAYD COMPT COMPS KSTD envd s) cp)
               (init_comps PAYD COMPT COMPS KSTD envd s)).
      apply IHcmd1 with (tr:=tr); auto.
      apply IHcmd2 with (tr:=tr); auto.
Qed.

Lemma hout_init : forall clblr init i s tr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init i s ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr).
Proof.
  intros clblr init i s tr Hinit Htr.
  inversion Hinit. subst s0.
  destruct (initial_init_state PAYD COMPT COMPS KSTD IENVD) as [ics [itr] ? ?]_eqn.
  assert (filter clblr ics = fold_right exec_comps nil (outputs clblr itr)).
    unfold initial_init_state in *. inversion Heqi0.
    apply f_equal with (f:=init_ktr _ _ _ _ _ ) in Heqi0.
    simpl in Heqi0. apply pack_injective in Heqi0. subst itr. auto.
  simpl. apply hout_init' with (tr:=itr); auto.
  subst s. auto.
Qed.

Lemma hout_hdlr' : forall clblr envd cc m s cmd input tr tr',
  ktr (hdlr_kst _ _ _ _ envd s) = [tr]%inhabited ->
  filter clblr (kcs (hdlr_kst _ _ _ _ _ s)) = fold_right exec_comps nil (outputs clblr tr) ->
  let s' := hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD cc m envd s cmd input in
  ktr (hdlr_kst _ _ _ _ _ s') = [tr']%inhabited ->
  filter clblr (kcs (hdlr_kst _ _ _ _ _ s')) = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr envd cc m s cmd input tr tr' Htr Heq s' Htr'. subst s'.
  generalize dependent s. generalize dependent tr. generalize dependent tr'.
  induction cmd; simpl; intros tr' tr s Htr Heq Htr'.
    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD cc m envd s
                 cmd1 (fst input)) as [ [? [itr] ?] ?]_eqn.
    apply IHcmd2 with (tr:=itr); auto.
    rewrite <- Heqh.
    apply IHcmd1 with (tr:=tr); auto.
    rewrite Heqh. auto.

    destruct (num_eq
                 (eval_hdlr_expr PAYD COMPT COMPS KSTD cc m
                    (kst PAYD COMPT COMPS KSTD
                       (hdlr_kst PAYD COMPT COMPS KSTD envd s))
                    (hdlr_env PAYD COMPT COMPS KSTD envd s) e) FALSE).
      apply IHcmd2 with (tr:=tr); auto.
      apply IHcmd1 with (tr:=tr); auto.

    
    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl.
    destruct (clblr
           (projT1
              (eval_hdlr_expr PAYD COMPT COMPS KSTD cc m
                 (kst PAYD COMPT COMPS KSTD hdlr_kst) hdlr_env e))); auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl.
    destruct (clblr
           {|
           comp_type := t;
           comp_fd := input;
           comp_conf := eval_hdlr_payload_expr PAYD COMPT COMPS KSTD cc m
                          (kst PAYD COMPT COMPS KSTD hdlr_kst) envd hdlr_env
                          (comp_conf_desc COMPT COMPS t) p |}); auto.
    simpl. f_equal. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in Htr'.
    apply pack_injective in Htr'. subst tr'. auto.

    destruct s. simpl in *.
    destruct (find_comp COMPT COMPTDEC COMPS
                  (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD cc m
                     (kst PAYD COMPT COMPS KSTD hdlr_kst) envd hdlr_env cp)
                  (Reflex.kcs _ _ _ _ hdlr_kst)).
      apply IHcmd1 with (tr:=tr); auto.
      apply IHcmd2 with (tr:=tr); auto.
Qed.

Lemma hout_hdlr : forall clblr cc m s s' input tr tr',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m input s s' ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr) ->
  ktr s' = [tr']%inhabited ->
  filter clblr (kcs s') = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr cc m s s' input tr tr' Hve Htr Heq Htr'.
  inversion Hve. subst s'0. unfold kstate_run_prog.
  destruct ((default_hdlr_state PAYD COMPT COMPS KSTD
                 (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr0)
                 (projT1 hdlrs))) as [ [ ? [itr] ? ] ? ]_eqn.
    apply hout_hdlr' with (tr:=itr); auto.
    rewrite <- Heqh. unfold default_hdlr_state, mk_inter_ve_st in Heqh.
    apply f_equal with (f:=fun s => ktr (hdlr_kst _ _ _ _ _ s)) in Heqh.
    simpl in *. apply pack_injective in Heqh. subst itr. simpl.
    unfold ktr in Htr. rewrite H0 in Htr. apply pack_injective in Htr.
    subst tr0. auto.
    unfold kstate_run_prog in *. rewrite Heqh in *.
    rewrite H3. auto.
Qed.

Lemma hout_hcs : forall clblr s tr,
  Reach s ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr).
Proof.
  intros clblr s tr HReach Htr.
  generalize dependent tr.
  induction HReach; intros tr Htr.
    eapply hout_init; eauto.

    destruct s as [? [itr] ?]_eqn.
    eapply hout_hdlr; eauto.

    inversion H. subst s'. simpl in *.
    apply pack_injective in Htr. subst tr.
    simpl. eapply IHHReach; eauto.
Qed.

Lemma hout_eq_hcs_eq : forall s s' clblr,
  Reach s -> Reach s' ->
  high_out_eq s s' clblr ->
  filter clblr (kcs s) = filter clblr (kcs s').
Proof.
  intros s s' clblr HReach HReach' Hout_eq.
  destruct s as [ ? [tr] ? ]; destruct s' as [ ? [tr'] ? ].
  rewrite hout_hcs with (tr:=tr); auto.
  rewrite hout_hcs with (tr:=tr'); auto.
  rewrite Hout_eq; auto.
Qed.

Lemma hfind_cs_filter : forall cs clblr cp,
  high_comp_pat COMPT COMPTDEC COMPS cp clblr ->
  find_comp COMPT COMPTDEC COMPS cp cs = 
  find_comp COMPT COMPTDEC COMPS cp (filter clblr cs).
Proof.
  intros cs clblr cp Hhigh.
  induction cs.
    auto.

    simpl. destruct (clblr a) as [ | ]_eqn. simpl.
    destruct (match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [ ? | ? ]_eqn; auto.
    destruct (match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [ ? | ? ]_eqn.
    unfold high_comp_pat, match_comp in Hhigh. specialize (Hhigh a).
    rewrite Heqo in Hhigh. specialize (Hhigh (Logic.eq_refl _)). congruence.
    auto.
Qed.

Lemma hout_eq_find_eq : forall cp s s' clblr,
  Reach s -> Reach s' ->
  high_out_eq s s' clblr ->
  high_comp_pat COMPT COMPTDEC COMPS cp clblr ->
  find_comp COMPT COMPTDEC COMPS cp (kcs s) = 
  find_comp COMPT COMPTDEC COMPS cp (kcs s').
Proof.
  intros cp s s' clblr HReach HReach' Hout_eq Hcp.
  rewrite hfind_cs_filter with (clblr:=clblr) (cs:=Reflex.kcs _ _ _ _ s); auto.
  rewrite hfind_cs_filter with (clblr:=clblr) (cs:=Reflex.kcs _ _ _ _ s'); auto.
  erewrite hout_eq_hcs_eq; auto.
Qed.

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
  unfold kstate_run_prog in H3.
  apply f_equal with (f:=ktr) in H1.
  simpl in H1.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt ?i) = _,
      Hmid : ktr _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt i trmid tr' lblr Hmid)
  end.
  subst s'.
  apply H4 in Htr'.
  destruct Htr'.
  destruct H3.
  subst tr'.
  match goal with
  |- inputs ?lblr (?x++?act1::?act2::?tr0) = _
    => replace (inputs lblr (x++act1::act2::tr0)) with
       (inputs lblr (act1::act2::tr0))
  end.
  simpl.
  unfold ktr in Htr.
  rewrite H0 in Htr.
  apply pack_injective in Htr.
  subst tr.
  rewrite Hhigh.
  auto.
  clear H4.
  induction x.
    auto.

    simpl in *.
    rewrite Hhigh in *.
    pose proof (H5 a).
    simpl in H3.
    pose proof (H3 (or_introl _ (Logic.eq_refl a))).
    rewrite H4.
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
  unfold kstate_run_prog in H3.
  apply f_equal with (f:=ktr) in H1.
  simpl in H1.
  match goal with
  | [ _ : hdlr_kst _ _ _ _ ?envd
                   (hdlr_state_run_cmd _ _ _ _ _ ?c ?m _ ?hst ?stmt ?i) = _,
      Hmid : ktr _ = [?trmid]%inhabited |- _ ]
    => pose proof (hdlr_no_recv c m envd hst stmt i trmid tr' lblr Hmid)
  end.
  subst s'.
  apply H4 in Htr'.
  destruct Htr'.
  destruct H3.
  subst tr'.
  match goal with
  |- inputs ?lblr (?x++?act1::?act2::?tr0) = _
    => replace (inputs lblr (x++act1::act2::tr0)) with
       (inputs lblr tr0)
  end.
  unfold ktr in Htr.
  rewrite H0 in Htr.
  apply pack_injective in Htr.
  subst tr.
  auto.

  induction x.
    simpl.
    rewrite Hhigh.
    auto.

    simpl in *.
    pose proof (H5 a).
    simpl in H3.
    pose proof (H3 (or_introl _ (Logic.eq_refl a))).
    rewrite H6.
    apply IHx; eauto.
Qed.

Theorem ni_suf : forall clblr vlblr cslblr,
  low_ok clblr vlblr cslblr ->
  high_ok clblr vlblr cslblr ->
  NI clblr vlblr cslblr.
Proof.
  unfold NI.
  intros clblr vlblr cslblr Hlow Hhigh s HReach.
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

      split.
        reflexivity.
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
        decompose [and] IHsnil.
        econstructor; eauto; eauto.
        pose proof (filter_In clblr c (Reflex.kcs _ _ _ _ snil_ind)) as [Hcs ?].
        apply Hcs. rewrite <- hout_eq_hcs_eq with (s:=s); subst snil_ind; auto.
        apply filter_In; auto. subst snil_ind; auto.

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
        pose proof (Hlow c m input s s' Hclblr HReach H) as Hss'.
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
          split.
            eapply IHsnil; eauto.
            unfold cs_eq in *.
            simpl in *. transitivity (filter cslblr (kcs s)).
            symmetry. eapply Hss'. eapply IHsnil.

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
        decompose [and] IHsnil.
        econstructor; eauto.
        pose proof (filter_In clblr c (Reflex.kcs _ _ _ _ snil_ind)) as [Hcs ?].
        apply Hcs. rewrite <- hout_eq_hcs_eq with (s:=s); subst snil_ind; auto.
        apply filter_In; auto. subst snil_ind; auto.

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