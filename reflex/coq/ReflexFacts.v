Require Import Reflex.
Require Import ReflexBase.
Require Import ActionMatch.

Lemma find_comp_suc_match :
  forall COMPT COMPTDEC COMPS cp cs c,
  find_comp COMPT COMPTDEC COMPS cp cs = Some c ->
  Reflex.match_comp COMPT COMPTDEC COMPS cp (projT1 c) = true /\
  List.In (projT1 c) cs.
Proof.
  intros COMPT COMPTDEC COMPS cp cs c Hfind.
  induction cs; simpl in Hfind.
    discriminate.

    destruct (Reflex.match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [? | ?]_eqn.
      unfold Reflex.match_comp. inversion Hfind. rewrite <- H0.
      simpl. rewrite Heqo. auto.

      simpl. tauto. 
Qed.

Lemma find_comp_fail :
  forall COMPT COMPTDEC COMPS cp cs,
  find_comp COMPT COMPTDEC COMPS cp cs = None ->
  forall c, List.In c cs ->
  Reflex.match_comp COMPT COMPTDEC COMPS cp c = false.
Proof.
  intros COMPT COMPTDEC COMPS cp cs Hfind c Hin.
  induction cs.
    contradiction.

    simpl in Hfind. destruct Hin.
      subst c. unfold Reflex.match_comp.
      destruct (Reflex.match_comp_pf COMPT COMPTDEC COMPS cp a)
        as [? | ?]_eqn; auto; discriminate.

      destruct (Reflex.match_comp_pf COMPT COMPTDEC COMPS cp a)
        as [? | ?]_eqn; auto; discriminate.
Qed.

Lemma elt_match_eltMatch_T : forall d e1 e2,
  eltMatch d e1 e2 <-> elt_match d e2 e1 = true.
Proof.
  intros d e1 e2.
  unfold eltMatch, elt_match.
  destruct e1.
    destruct d;
      match goal with
      |- context [ if ?e then _ else _ ] =>
        destruct e; intuition; try discriminate
      end.

    tauto.
Qed.

Lemma elt_match_eltMatch_F : forall d e1 e2,
  ~eltMatch d e1 e2 <-> elt_match d e2 e1 = false.
Proof.
  intros d e1 e2.
  unfold eltMatch, elt_match.
  destruct e1.
    destruct d;
      match goal with
      |- context [ if ?e then _ else _ ] =>
        destruct e; intuition; try discriminate
      end.

    intuition.
Qed.

Lemma match_comp_equiv :
  forall COMPT COMPS COMPTDEC cp c,
  Reflex.match_comp COMPT COMPTDEC COMPS cp c = true <->
  ActionMatch.match_comp COMPT COMPS COMPTDEC (Some cp) c.
Proof.
  intros COMPT COMPS COMPTDEC cp c.
  unfold Reflex.match_comp, ActionMatch.match_comp,
    Reflex.match_comp_pf, ActionMatch.match_comp'.
  destruct c as [ct ? cfg]; destruct cp as [cpt cpfg]; simpl.
  destruct (COMPTDEC ct cpt). destruct e.
  destruct (comp_conf_desc COMPT COMPS ct) as [n vd].
  induction n.
    simpl in *. intuition.

    simpl in *. destruct vd. destruct cfg. destruct cpfg.
    simpl.
    match goal with
    |- context[ elt_match ?d ?e1 ?e2 ]
      => destruct (elt_match d e1 e2) as [? | ?]_eqn
    end; simpl.
      apply elt_match_eltMatch_T in Heqb.
      intuition; apply IHn; auto.

    split.
      discriminate.

      intro H. destruct H.
      apply elt_match_eltMatch_F in Heqb.
      auto.

  intuition.
Qed.

Lemma find_comp_suc_match_prop :
  forall COMPT COMPTDEC COMPS cp cs c,
  find_comp COMPT COMPTDEC COMPS cp cs = Some c ->
  ActionMatch.match_comp COMPT COMPS COMPTDEC (Some cp) (projT1 c) /\
  List.In (projT1 c) cs.
Proof.
  intros. rewrite <- match_comp_equiv.
  apply find_comp_suc_match; auto.
Qed.

Lemma find_comp_fail_prop :
  forall COMPT COMPTDEC COMPS cp cs,
  find_comp COMPT COMPTDEC COMPS cp cs = None ->
  forall c, List.In c cs ->
  ~ActionMatch.match_comp COMPT COMPS COMPTDEC (Some cp) c.
Proof.
    intros. rewrite <- match_comp_equiv.
    apply Bool.not_true_iff_false.
    eapply find_comp_fail; eauto.
Qed.

Lemma comp_inv : forall COMPT COMPS ct cfd1 cfd2 cfg1 cfg2,
  Build_comp COMPT COMPS ct cfd1 cfg1 = Build_comp COMPT COMPS ct cfd2 cfg2 ->
  cfd1 = cfd2 /\ cfg1 = cfg2.
Proof.
  intros COMPT COMPS ct cfd1 cfd2 cfg1 cfg2 Heq.
  inversion Heq.
  apply Eqdep.EqdepTheory.inj_pair2 in H1; auto.
Qed.

Lemma seq_rew_init :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC envd cmd1 cmd2 s input,
  init_state_run_cmd _ _ COMPTDEC _ _ envd s (Seq PAYD COMPT COMPS KSTD _ _ cmd1 cmd2) input =
  init_state_run_cmd _ _ COMPTDEC _ _ envd
    (init_state_run_cmd _ _ COMPTDEC _ _ envd s cmd1 (fst input)) cmd2 (snd input).
Proof.
  auto.
Qed.

Lemma seq_rew : forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC c m envd cmd1 cmd2 s input,
  hdlr_state_run_cmd _ _ COMPTDEC _ _ c m envd s (Seq PAYD COMPT COMPS KSTD _ _ cmd1 cmd2) input =
  hdlr_state_run_cmd _ _ COMPTDEC _ _ c m envd
    (hdlr_state_run_cmd _ _ COMPTDEC _ _ c m envd s cmd1 (fst input)) cmd2 (snd input).
Proof.
  auto.
Qed.

Lemma complkup_rew_init :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC envd cp cmd1 cmd2 s i,
  init_state_run_cmd _ _ COMPTDEC _ _ envd s (CompLkup PAYD COMPT COMPS KSTD _ _ cp cmd1 cmd2) i =
      match find_comp COMPT COMPTDEC COMPS
          (eval_base_comp_pat COMPT COMPS envd
             (init_env _ _ _ _ envd s) cp)
          (init_comps _ _ _ _ envd s) with
      | Some cdp =>
          let c := projT1 cdp in
          let d :=
            Comp COMPT (comp_pat_type COMPT COMPS (base_term COMPT) envd cp) in
          let new_envd :=
            existT (ReflexVec.svec (cdesc COMPT)) (S (projT1 envd))
              (ReflexVec.svec_shift d (projT2 envd)) in
          let s' :=
            Build_init_state _ _ _ _ new_envd
                             (init_comps _ _ _ _ envd s)
                             (init_ktr _ _ _ _ envd s)
                             (ReflexHVec.shvec_shift (sdenote_cdesc COMPT COMPS) d
                                                     (existT
                                                        (fun c0 : comp COMPT COMPS =>
                                                           comp_type COMPT COMPS c0 =
                                                           conc_pat_type COMPT COMPS
                                                                         (eval_base_comp_pat COMPT COMPS envd
                                                                                             (init_env _ _ _ _ envd s)
                                                                                             cp)) c (projT2 cdp)) 
                                                     (projT2 envd)
                                                     (init_env _ _ _ _ envd s))
                             (init_kst _ _ _ _ envd s) in
          let s'' := init_state_run_cmd _ _ COMPTDEC _ _ new_envd s' cmd1 (fst i) in
          {|
          init_comps := init_comps _ _ _ _ new_envd s'';
          init_ktr := init_ktr _ _ _ _ new_envd s'';
          init_env := ReflexHVec.shvec_unshift (cdesc COMPT)
                        (sdenote_cdesc COMPT COMPS) 
                        (projT1 envd) d (projT2 envd)
                        (init_env _ _ _ _ new_envd s'');
          init_kst := init_kst _ _ _ _ new_envd s'' |}
      | None => init_state_run_cmd _ _ COMPTDEC _ _ envd s cmd2 (snd i)
      end.
Proof.
  auto.
Qed.

Lemma complkup_rew_hdlr :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC cc m envd0 cp cmd1 cmd2 s0 i,
  hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m envd0 s0
                     (CompLkup PAYD COMPT COMPS KSTD _
                               envd0 cp cmd1 cmd2) i =
      match find_comp COMPT COMPTDEC COMPS
          (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD cc m
             (kst PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0)) envd0 (hdlr_env _ _ _ _ _ s0) cp)
          (kcs PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0)) with
      | Some cdp =>
          let c := projT1 cdp in
          let d :=
            Comp COMPT
              (comp_pat_type COMPT COMPS _
                 (*(hdlr_term PAYD COMPT COMPS KSTD (CT COMPT COMPS c)
                    (CTAG PAYD m))*) envd0 cp) in
          let new_envd :=
            existT (ReflexVec.svec (cdesc COMPT)) (S (projT1 envd0))
              (ReflexVec.svec_shift d (projT2 envd0)) in
          let s'0 :=
            Build_hdlr_state _ _ _ _ new_envd
                       {|
                        kcs := kcs PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0);
                        ktr := ktr PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0);
                        kst := kst PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0) |}
                       (ReflexHVec.shvec_shift (sdenote_cdesc COMPT COMPS) d
                          (existT
                             (fun c0 : comp COMPT COMPS =>
                              comp_type COMPT COMPS c0 =
                              conc_pat_type COMPT COMPS
                                (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD cc
                                   m (kst PAYD COMPT COMPS KSTD (hdlr_kst _ _ _ _ _ s0)) envd0
                                   (hdlr_env _ _ _ _ _ s0) cp)) c (projT2 cdp)) 
                          (projT2 envd0) (hdlr_env _ _ _ _ _ s0) ) in
          let s'' := hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m new_envd s'0 cmd1 (fst i) in
          {|
          hdlr_kst := hdlr_kst PAYD COMPT COMPS KSTD new_envd s'';
          hdlr_env := ReflexHVec.shvec_unshift (cdesc COMPT)
                        (sdenote_cdesc COMPT COMPS) 
                        (projT1 envd0) d (projT2 envd0)
                        (hdlr_env PAYD COMPT COMPS KSTD new_envd s'') |}
      | None => hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m envd0 s0 cmd2 (snd i)
      end.
Proof.
  simpl. destruct s0. auto.
Qed.

Lemma ite_rew_init :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC envd0 cond cmd1 cmd2 s0 i,
  init_state_run_cmd _ _ COMPTDEC _ _ envd0 s0 (Ite PAYD COMPT COMPS KSTD _ _ cond cmd1 cmd2) i =
  if ReflexBase.num_eq
           (eval_base_expr COMPT COMPS
              (init_env _ _ _ _ envd0 s0) cond)
           (ReflexBase.Num "000" "000")
      then init_state_run_cmd _ _ COMPTDEC _ _ envd0 s0 cmd2 (snd i)
      else init_state_run_cmd _ _ COMPTDEC _ _ envd0 s0 cmd1 (fst i).
Proof.
  auto.
Qed.

Lemma ite_rew_hdlr :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPS KSTD COMPTDEC cc m envd0 cond cmd1 cmd2 s0 i,
  hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m envd0 s0 (Ite PAYD COMPT COMPS KSTD _ _ cond cmd1 cmd2) i =
        if ReflexBase.num_eq
           (eval_hdlr_expr _ COMPT COMPS KSTD cc m
              (kst _ COMPT COMPS KSTD
                 (hdlr_kst _ COMPT COMPS KSTD envd0 s0))
              (hdlr_env _ COMPT COMPS KSTD envd0 s0) cond)
           (ReflexBase.Num "000" "000")
      then hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m envd0 s0 cmd2 (snd i)
      else hdlr_state_run_cmd _ _ COMPTDEC _ _ cc m envd0 s0 cmd1 (fst i).
Proof.
  auto.
Qed.

Lemma comp_in_ve :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPTDEC COMPS KSTD HANDLERS s s' cc m i c,
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m i s s' ->
  List.In c (kcs _ _ _ _ s) -> List.In c (kcs _ _ _ _ s').
Proof.
  intros NB_MSG PAYD COMPT COMPTDEC COMPS KSTD HANDLERS s s' cc m i c Hve Hin.
  destruct Hve. subst hdlrs.
  destruct (HANDLERS (tag PAYD m) (comp_type COMPT COMPS cc)) as [envd cmd].
  subst s'. simpl in *. unfold kstate_run_prog.
  assert (forall c,
    List.In c (kcs _ _ _ _ s) ->
    List.In c (kcs _ _ _ _ (hdlr_kst _ _ _ _ _
                (default_hdlr_state PAYD COMPT COMPS KSTD
                (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd)))) as Hcs by auto.
  revert Hcs. revert Hin.
  generalize (default_hdlr_state PAYD COMPT COMPS KSTD
    (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd).
  intros s' Hin Hcs.
  generalize dependent c.
  induction cmd; simpl in *; auto.
    destruct i as [i1 i2].
    match goal with
    |- context[ if ?e then _ else _ ]
      => destruct e
    end; eauto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *;
    match goal with
    |- context[ match ?e with | Some _ => _ | None => _ end ]
      => destruct e
    end; simpl in *; eauto.
Qed.

Lemma comp_in_prop :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPTDEC COMPS KSTD HANDLERS s s'
         (P:comp _ _ -> Prop) cc m i,
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m i s s' ->
  (forall c, List.In c (kcs _ _ _ _ s') -> P c) ->
  forall c, List.In c (kcs _ _ _ _ s) -> P c.
Proof.
  intros NB_MSG PAYD COMPT COMPTDEC COMPS KSTD HANDLERS s s' P cc m i Hve Hin c ?.
  apply Hin. eapply comp_in_ve; eauto.
Qed.

Fixpoint no_spawn {NB_MSG} {PAYD:vvdesc NB_MSG} {COMPT:Set}
         (COMPTDEC:forall (x y : COMPT), decide (x = y))
         {COMPS KSTD envd term}
         ct (c:cmd PAYD COMPT COMPS KSTD term envd) :=
  match c with
  | Reflex.Spawn _ ct' _ _ _ =>
    if COMPTDEC ct ct'
    then False
    else True
  | Reflex.Seq _ c1 c2 =>
    no_spawn COMPTDEC ct c1 /\ no_spawn COMPTDEC ct c2
  | Reflex.Ite _ _ c1 c2 =>
    no_spawn COMPTDEC ct c1 /\ no_spawn COMPTDEC ct c2
  | Reflex.CompLkup _ _ c1 c2 =>
    no_spawn COMPTDEC ct c1 /\ no_spawn COMPTDEC ct c2
  | _ => True
  end.

Lemma no_spawn_cs :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPTDEC COMPS KSTD HANDLERS s s' cc m i c,
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m i s s' ->
  no_spawn COMPTDEC (comp_type _ _ c) (projT2 (HANDLERS (tag _ m) (comp_type _ _ cc))) ->
  List.In c (kcs _ _ _ _ s') ->
  List.In c (kcs _ _ _ _ s).
Proof.
  intros NB_MSG PAYD COMPT COMPTDEC COMPS KSTD HANDLERS
         s s' cc m i c Hve Hno_spawn Hin.
  destruct Hve. subst hdlrs.
  destruct (HANDLERS (tag PAYD m) (comp_type COMPT COMPS cc)) as [envd cmd].
  subst s'. unfold kstate_run_prog in *. simpl in *.
  assert (List.In c (kcs _ _ _ _ (hdlr_kst _ _ _ _ _
                (default_hdlr_state PAYD COMPT COMPS KSTD
                (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd))) ->
          List.In c (kcs _ _ _ _ s)) as Hcs by auto.
  revert Hin Hcs.
  generalize (default_hdlr_state PAYD COMPT COMPS KSTD
    (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd).
  intros s' Hin Hcs.
  generalize dependent c.
  induction cmd; intros; auto; simpl in *.
    destruct i as [i1 i2].
    destruct Hno_spawn.
    eauto.

    destruct i as [i1 i2].
    destruct Hno_spawn.
    match type of Hin with
    | context [ if ?e then _ else _ ]
      => destruct e
    end; eauto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *;
    destruct c; simpl in *;
    destruct (COMPTDEC comp_type t);
    destruct Hin; try contradiction;
    try congruence; auto.

    destruct s'; simpl in *; auto.

    destruct s'; simpl in *; auto.

    destruct i as [i1 i2].
    destruct Hno_spawn.
    destruct s'; simpl in *.
    match type of Hin with
    | context [ match ?e with | Some _ => _ | None => _ end ]
      => destruct e
    end; eauto.
Qed.

Fixpoint no_stupd {NB_MSG} {PAYD:vvdesc NB_MSG} {COMPT:Set}
         {COMPS KSTD envd term}
         (c:cmd PAYD COMPT COMPS KSTD term envd) :=
  match c with
  | Reflex.Seq _ c1 c2 =>
    no_stupd c1 /\ no_stupd c2
  | Reflex.Ite _ _ c1 c2 =>
    no_stupd c1 /\ no_stupd c2
  | Reflex.CompLkup _ _ c1 c2 =>
    no_stupd c1 /\ no_stupd c2
  | Reflex.StUpd _ _ _ => False
  | _ => True
  end.

Lemma no_stupd_kst :
  forall NB_MSG (PAYD:vvdesc NB_MSG) COMPT COMPTDEC COMPS KSTD HANDLERS s s' cc m i,
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m i s s' ->
  no_stupd (projT2 (HANDLERS (tag _ m) (comp_type _ _ cc))) ->
  kst _ _ _ _ s' = kst _ _ _ _ s.
Proof.
  intros NB_MSG PAYD COMPT COMPTDEC COMPS KSTD HANDLERS
         s s' cc m i Hve Hno_stupd.
  destruct Hve. subst hdlrs.
  destruct (HANDLERS (tag PAYD m) (comp_type COMPT COMPS cc)) as [envd cmd].
  subst s'. unfold kstate_run_prog in *. simpl in *.
  assert (kst _ _ _ _ (hdlr_kst _ _ _ _ _ (default_hdlr_state PAYD COMPT COMPS KSTD
              (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd)) =
          kst _ _ _ _ s) as Hst by auto.
  revert Hst.
  generalize (default_hdlr_state PAYD COMPT COMPS KSTD
    (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr) envd).
  induction cmd; intros; auto; simpl in *.
    destruct i as [i1 i2].
    destruct Hno_stupd.
    erewrite IHcmd2; eauto.

    destruct i as [i1 i2].
    destruct Hno_stupd.
    match goal with
    |- context [ if ?e then _ else _ ]
      => destruct e
    end; eauto.

    destruct h; simpl in *; auto.

    destruct h; simpl in *; auto.

    destruct h; simpl in *; auto.

    contradiction.

    destruct i as [i1 i2].
    destruct Hno_stupd.
    destruct h; simpl in *.
    match goal with
    |- context [ match ?e with | Some _ => _ | None => _ end ]
      => destruct e
    end; eauto.
      simpl in *. erewrite IHcmd1; eauto.
Qed.