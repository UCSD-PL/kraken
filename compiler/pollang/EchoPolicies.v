Require Import Reflex.
Require Import ReflexEcho.
Import Spec.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.

Theorem recv_before : forall st tr m,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmBefore PAYD COMPT COMPS COMPTDEC
            (KORecv PAYD COMPT COMPS None
                     (Some (Build_opt_msg PAYD
                                          None (Some m, tt))))
            (KOSend PAYD COMPT COMPS None
                     (Some (Build_opt_msg PAYD
                                          None (Some m, tt))))
            tr.
Proof.
  intros;
  match goal with
  | [ _ : ktr _ _ _ _ _ = inhabits ?tr, H : Reach _ _ _ _ _ _ _ _ _ |- _ ]
      => generalize dependent tr; induction H;
         (*Do not put simpl anywhere in here. It breaks destruct_unpack.*)
         intros; destruct_unpack
  end.
match_immbefore.

Qed.

Theorem send_after : forall st tr m,
  Reach st -> ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
            (KOSend PAYD None
                     (Some (Build_opt_msg PAYD
                                           None (Some m, tt))))
            (KORecv PAYD None
                     (Some (Build_opt_msg PAYD
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.
