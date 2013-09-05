Require Import Reflex.

Lemma find_comp_suc_match :
  forall COMPT COMPTDEC COMPS cp cs c,
  find_comp COMPT COMPTDEC COMPS cp cs = Some c ->
  match_comp COMPT COMPTDEC COMPS cp (projT1 c) = true.
Proof.
  intros COMPT COMPTDEC COMPS cp cs c Hfind.
  induction cs; simpl in Hfind.
    discriminate.

    destruct (match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [? | ?]_eqn.
      unfold match_comp. inversion Hfind. rewrite <- H0.
      simpl. rewrite Heqo. auto.

      auto.
Qed.