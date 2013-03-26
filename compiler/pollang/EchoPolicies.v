Require Import Reflex.
Require Import ReflexEcho.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.

Theorem recv_before : forall st tr m,
  Reach _ _ COMPS _ _ _ INIT HANDLERS st -> ktr _ _ _ _ st = inhabits tr ->
  ImmBefore PAYD
            (KORecv PAYD None
                     (Some (Build_opt_msg PAYD
                                           None (Some m, tt))))
            (KOSend PAYD None
                     (Some (Build_opt_msg PAYD
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.

Theorem send_after : forall st tr m,
  Reach _ _ COMPS _ _ _ INIT HANDLERS st -> ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD
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
