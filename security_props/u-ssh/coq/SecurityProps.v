Require Import Kernel.
Require Import List.
Require Import Message.
Require Import Ynot.
Require Import Ascii.

(*Cannot create PTY until authenticated for that user*)
Inductive userauth : [KTrace] -> Prop :=
| ua_empty       : userauth [nil]%inhabited
| non_create_pty : forall tr act,
                     userauth [tr] ->
                     (forall c u, act <> KSend c (SysCreatePtyerReq u)) ->
                     userauth [act :: tr]
| create_pty     : forall c tr autheduser n,
                     userauth [tr] ->
                     n <> 0 ->
                     (exists sys, projT1 sys = System /\
                     In (KRecv sys (SysLoginRes autheduser (num_of_nat n))) tr) ->
                     userauth [KSend c (SysCreatePtyerReq autheduser) :: tr].

Theorem KI_userauth : forall st,
  KInvariant st -> userauth (ktr st).
Proof.
  intros st HKI.
  induction HKI; simpl in *.
    (*KI_init*)
    repeat econstructor; discriminate.

    (*KI_select*)
    destruct (ktr s); simpl; constructor; [auto | discriminate].

    (*KI_exchange*)
    inversion H; remember (ktr s) as ktrs; destruct ktrs; simpl in *;
    try (repeat constructor; [auto | discriminate]);
    try (repeat constructor; [auto | discriminate | discriminate]).
    apply create_pty with (n:=nat_of_num (loginsucceded s)).
    constructor; [assumption | discriminate].
    assumption.
    clear H IHHKI H2 H1 s' CT.
    generalize dependent k.
    induction HKI; simpl in *; intros.
      (*KI_init*)
      firstorder. (*H0 is false. Magically, this tactic infers that.*)

      (*KI_select*)
      destruct (ktr s); apply IHHKI with (k:=k0) in H0;
      [ simpl in *; apply pack_injective in Heqktrs; rewrite Heqktrs;
        simpl in *; destruct H0; exists x; tauto
      | reflexivity ].

      (*KI_exchange*)
      inversion H; simpl in *;
      match goal with
      | [s' : kstate, Hs : _ = ?s', H0 : _ <> 0 |- _]
          => destruct (ktr s); destruct Hs; simpl in *;
             apply IHHKI with (k:=k0) in H0;
             [ simpl in *; apply pack_injective in Heqktrs; rewrite Heqktrs;
               simpl in *; destruct H0; exists x; tauto
             | reflexivity ]
      | [ |- _ ] => destruct (ktr s); destruct H2; simpl in *;
                    apply pack_injective in Heqktrs; rewrite Heqktrs;
                    exists c0; rewrite num_nat_embedding; simpl; tauto
      end.
Qed.

(*Exactly n authentication attempts*)
Inductive auth_attempts : nat -> [KTrace] -> Prop :=
| naa_empty   : auth_attempts 0 [nil]%inhabited
| non_attempt : forall n tr act,
                  auth_attempts n [tr] ->
                  (forall c accstr, act <> KSend c (SysLoginReq accstr) )->
                  auth_attempts n [act :: tr]
| attempt     : forall c n tr accstr,
                  auth_attempts n [tr] ->
                  auth_attempts (S n) [KSend c (SysLoginReq accstr) :: tr].

Theorem auth_att_3 : forall st,
  KInvariant st -> (exists n, n <=3 /\ auth_attempts n (ktr st)).
Proof.
  intros st HKI.
  exists (nat_of_num (logincnt st)).
  split.
    (*nat_of_num (logincnt st) <= 3*)
    induction HKI; simpl in *.
      auto.

      assumption.

      destruct H; simpl; try assumption.
        destruct IHHKI.
          destruct H.
          reflexivity.

          admit. (*Again not sure how to handle nat_of_num, num_of_nat*)

    (*nat_of_num (logincnt st) auth attempts*)
    induction HKI; simpl in *.
      repeat constructor; discriminate.

      destruct (ktr s); simpl; constructor; [auto | discriminate].

      inversion H; destruct (ktr s); simpl in *;
      try (repeat constructor; [auto | discriminate]);
      try (repeat constructor; [auto | discriminate | discriminate]).
      admit. (*Not sure how to handle nat_of_num, num_of_nat*)
Qed.
