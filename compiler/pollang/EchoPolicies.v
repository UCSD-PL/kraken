Require Import Reflex.
Require Import ReflexEcho.
Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.

Theorem recv_before : forall st tr m,
  Reach _ _ COMPS _ _ INIT HANDLERS st -> ktr _ _ st = inhabits tr ->
  ImmBefore NB_MSG PAYD
            (@KORecv NB_MSG PAYD None
                     (Some (@Build_opt_msg NB_MSG PAYD
                                           None (Some m, tt))))
            (@KOSend NB_MSG PAYD None
                     (Some (@Build_opt_msg NB_MSG PAYD
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.

Theorem send_after : forall st tr m,
  Reach _ _ COMPS _ _ INIT HANDLERS st -> ktr _ _ st = inhabits tr ->
  ImmAfter NB_MSG PAYD
            (@KOSend NB_MSG PAYD None
                     (Some (@Build_opt_msg NB_MSG PAYD
                                           None (Some m, tt))))
            (@KORecv NB_MSG PAYD None
                     (Some (@Build_opt_msg NB_MSG PAYD
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.