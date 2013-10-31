Require Import Reflex.
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