Require Import ReflexEcho.
Require Import PolLang.
Require Import ActionMatch.
Require Import Reflex.
Require Import Tactics.

Theorem recv_before : forall st tr m,
  Reach _ _ INIT HANDLERS st -> ktr _ st = inhabits tr ->
  ImmBefore NB_MSG PAY_DESC
            (@KORecv NB_MSG PAY_DESC None
                     (Some (@Build_opt_msg NB_MSG PAY_DESC
                                           None (Some m, tt))))
            (@KOSend NB_MSG PAY_DESC None
                     (Some (@Build_opt_msg NB_MSG PAY_DESC
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.

Theorem send_after : forall st tr m,
  Reach _ _ INIT HANDLERS st -> ktr _ st = inhabits tr ->
  ImmAfter NB_MSG PAY_DESC
            (@KOSend NB_MSG PAY_DESC None
                     (Some (@Build_opt_msg NB_MSG PAY_DESC
                                           None (Some m, tt))))
            (@KORecv NB_MSG PAY_DESC None
                     (Some (@Build_opt_msg NB_MSG PAY_DESC
                                           None (Some m, tt))))
            tr.
Proof.
  crush.
Qed.