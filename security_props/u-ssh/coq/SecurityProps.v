Require Import Kernel.
Require Import List.
Require Import Message.
Require Import Ynot.
Require Import Ascii.
Require Import NPeano.
Require Import Arith.

Local Transparent nat_of_num num_of_nat.

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
                     (exists sys,
                        In (KRecv sys (SysLoginRes autheduser (num_of_nat n))) tr
                        /\ projT1 sys = System) ->
                     userauth [KSend c (SysCreatePtyerReq autheduser) :: tr].

Ltac rewrite_trace :=
  match goal with
  | [ H : [_]%inhabited = [_]%inhabited |- _ ]
    => apply pack_injective in H; rewrite H; simpl in *
  | [ tr := ktr ?s, H : [?k]%inhabited = (_ ~~~ _ :: _) |- _ ]
    => destruct (ktr s); simpl in *;
       rewrite_trace
  | [ H : {| components:= _ ;
             ktr := inhabit_unpack (ktr ?s) _ ;
             system := _ ;
             slave := _ ;
             logincnt := _ ;
             loginsucceded := _ ;
             username := _ |} = ?s' |- _ ]
    => destruct (ktr s); destruct H; simpl in *;
       rewrite_trace
  end.

Theorem KI_userauth : forall st,
  KInvariant st -> userauth (ktr st).
Proof.
  intros st HKI.
  induction HKI; simpl in *.
    (*KI_init*)
    repeat constructor; discriminate.

    (*KI_select*)
    destruct (ktr s); simpl; constructor; easy.

    (*KI_exchange*)
    inversion H; remember (ktr s) as ktrs; destruct ktrs; simpl in *;
    try (repeat constructor; auto || discriminate).
    eapply create_pty with (n:=nat_of_num (loginsucceded s)).
    constructor; [assumption | discriminate].
    assumption.
    clear H IHHKI H2 H1 s' CT.
    generalize dependent k.
    induction HKI; simpl in *; intros.
      (*KI_init*)
      intuition. (*H0 is false. Magically, this tactic infers that.*)

      (*KI_select*)
      rewrite_trace;
      apply IHHKI with (k:=k0) in H0;
      [ destruct H0 as [sys]; exists sys; tauto
      | reflexivity ].

      (*KI_exchange*)
      inversion H; rewrite_trace;
      match goal with
      | [ H : nat_of_num (loginsucceded s) <> 0 |- _ ]
          => apply IHHKI with (k:=k0) in H;
             [ destruct H as [sys]; exists sys; tauto
             | reflexivity ]
      | [ CT : projT1 ?c = System |- _ ]
          => exists c; rewrite num_nat_embedding;
             tauto
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

Ltac nat_num :=
  match goal with
  | [ |- context[ nat_of_ascii ( ascii_of_nat (_) )] ]
      => simpl; rewrite nat_ascii_embedding; nat_num
  | [ |- context[ _ mod _ ] ]
      => simpl; rewrite mod_small; nat_num
  | [ |- context[ _ / _ ] ]
      => simpl; rewrite div_small; nat_num
  | [ |- _ ]
      => simpl; try omega
  end.

Theorem auth_att_3 : forall st,
  KInvariant st -> (exists n, n <=3 /\ auth_attempts n (ktr st)).
Proof.
  intros st HKI.
  exists (nat_of_num (logincnt st)).
  induction HKI; simpl in *.
    split; [ omega | repeat constructor; discriminate].

    split; [ tauto
           | destruct (ktr s); simpl; constructor;
             [ tauto | discriminate ] ].

    inversion H; destruct (ktr s); simpl in *; split;
    try tauto; try (repeat constructor; tauto || discriminate);

      nat_num.

      rewrite plus_0_r.
      rewrite plus_comm.
      apply attempt.
      constructor.
      tauto.
      discriminate.
Qed.

Definition not_att (act : KAction) : bool :=
  match act with
  | KSend _ (SysLoginReq _) => true
  | _                       => false
  end.

Theorem auth_att_equiv : forall tr n,
  auth_attempts n [(filter not_att tr)] <-> auth_attempts n [tr].
Proof.
  (*intros tr n Hauth.
  generalize dependent n.
  induction tr; simpl in *.
    auto.

    destruct a; simpl in *;
      try (constructor; auto || discriminate).

      destruct m; simpl in *;
        try (constructor; auto || discriminate).

        intros n' Hauth.
        simple inversion Hauth; simpl in *.
          apply pack_injective in H0; inversion H0.

          apply pack_injective in H2.
          inversion H2.
          intros.
          contradict H4.
          eauto.

          rewrite <- H0.
          apply pack_injective in H1.
          inversion H1.
          intro.
          apply attempt.
          auto.
Qed.*)
Admitted.

Theorem auth_att_contra : forall n st,
  n >= 4 -> auth_attempts n (ktr st) -> ~ KInvariant st.
Proof.
  intro n.
  induction n.
    intros; omega.

    intros st Hn Hauth.
    simple inversion Hauth.
      discriminate.

      intros Hauth' Hact.
Admitted.

Theorem auth_att_3' : forall st n,
  KInvariant st -> auth_attempts n (ktr st) -> n <= 3.
Proof.
  intros st n KI Hauth.
  induction KI; simpl in *.
    simple inversion Hauth.
      omega.
      
      apply pack_injective in H2.
      inversion H2.
      intro Hauth2.
      simple inversion Hauth2.
        apply pack_injective in H4; inversion H4.
        admit.
        admit.
        apply pack_injective in H1; inversion H1.

    destruct (ktr s); simpl in *; simple inversion Hauth.
      omega.

      apply pack_injective in H2; inversion H2.
      intros Hauth2 Hact.
      rewrite H1 in Hauth2.
      auto.

      apply pack_injective in H1; inversion H1.

    destruct H; simpl in *. 

Admitted.
