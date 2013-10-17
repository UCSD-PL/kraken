Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language.

Require Import PolLang.
Require Import ActionMatch.
Require Import List.

Local Opaque str_of_string.

Theorem enable : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS None
                  (Some (Build_opt_msg PAYD M1 tt)))
          (KOSend PAYD COMPT COMPS None
                  (Some (Build_opt_msg PAYD M2 tt)))
          tr.
Proof.
  Time crush.
  clear_useless_hyps.
  repeat apply cut_exists.
  unfold cs in *.
  clear cs.
  revert H1.
  generalize dependent tr.
  induction H.

  unpack. intuition congruence.

  unpack; try solve [repeat apply cut_exists; eapply IHReach; eauto].
  releaser_match.

  unpack; try solve [repeat apply cut_exists; eapply IHReach; eauto].
Qed.
