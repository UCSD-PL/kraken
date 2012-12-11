Require Import Kernel.
Require Import List.
Require Import Message.
Require Import Ynot.
Require Import Ascii.

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

Ltac ve_steps_ua :=
  match goal with
  | [ IHHKI : userauth (ktr ?s) |- userauth (inhabit_unpack (ktr ?s)
                                                   (fun tr : KTrace =>
                                                    KSend _ _ :: KRecv _ _ :: _))]
      => destruct (ktr s);
         simpl;
         econstructor;
         [ econstructor; [apply IHHKI | discriminate]
         | discriminate]
  | [ IHHKI : userauth (ktr ?s) |- userauth (inhabit_unpack (ktr ?s)
                                                   (fun tr : KTrace =>
                                                    KRecv _ _ :: tr))]
      => destruct (ktr s);
         simpl;
         econstructor;
         [apply IHHKI | discriminate]
  end.

Ltac ve_pty_ua :=
 match goal with
  | [ CT : projT1 ?c = System, s : kstate, s' : kstate, resnum : num,
      H : _ = ?s', Heqktrs : [?k]%inhabited = ktr ?s' |- _ ]
      => apply f_equal with (f:=ktr) in H;
         simpl in H;
         rewrite <- Heqktrs in H;
         apply pack_injective in H;
         rewrite <- H;
         exists c;
         simpl;
         auto
  | [ s' : kstate, Hs' : _ = ?s', Heqktrs : [?k]%inhabited = ktr ?s',
     Hneq0 : nat_of_num (loginsucceded ?s') <> 0,
     IHHKI : _ -> forall k : KTrace, [_]%inhabited = [?k0]%inhabited -> _ |- _ ]
      => inversion Hs' as [Hs''];
        apply f_equal with (f:=ktr) in Hs'';
        simpl in Hs'';
        rewrite <- Heqktrs in Hs'';
        apply pack_injective in Hs'';
        rewrite <- Hs'';
        simpl;
           apply f_equal with (f:=loginsucceded) in Hs';
           simpl in Hs';
           rewrite <- Hs' in Hneq0;
           eapply IHHKI with (k:=k0) in Hneq0
  end.

Ltac ve_pty_ua' H2 Heqktrs H0 IHHKI k0 :=
 inversion H2 as [Hs''];
        apply f_equal with (f:=ktr) in Hs'';
        simpl in Hs'';
        rewrite <- Heqktrs in Hs'';
        apply pack_injective in Hs'';
        rewrite <- Hs'';
        simpl;
           apply f_equal with (f:=loginsucceded) in H2;
           simpl in H2;
           rewrite <- H2 in H0;
           eapply IHHKI with (k:=k0) in H0;
           [destruct H0 as [x [Hproj Hright]];
            destruct Hright;
            [discriminate | exists x; auto]
           | auto].


Theorem KI_userauth : forall st,
  KInvariant st -> userauth (ktr st).
Proof.
  intros st HKI.
  induction HKI; simpl in *.
    (*KI_init*)
    repeat econstructor; discriminate.

    (*KI_select*)
    remember tr as ktr.
    destruct ktr.
    simpl.
    econstructor.
    rewrite Heqktr.
    auto.
    discriminate.

    (*KI_exchange*)
    inversion H; simpl in *; try ve_steps_ua.
    (*We're left with only one valid exchange constructor,*)
    (*namely when the Kernel sends a SysCreatePtyerReq*)
    (*message.*)
    remember (ktr s) as ktrs.
    destruct ktrs.
    simpl.
    eapply create_pty.
    eapply non_create_pty.
    apply IHHKI.
    discriminate.
    apply H0.
    rewrite num_nat_embedding.
    (*Now we've reduced this to showing that the username*)
    (*was authenticated in the past.*)
    clear H IHHKI H2 H1 s'.
    generalize dependent k.
    induction HKI; simpl in *; intros.
      (*KI_init*)
      firstorder. (*H0 is false, but I don't know why this tactic works*)

      (*KI_select*)
      remember (ktr s) as ktrs'.
      destruct ktrs'.
      apply IHHKI with (k:=k0) in H0.
      simpl in Heqktrs.
      apply pack_injective in Heqktrs.
      rewrite Heqktrs.
      firstorder.
      reflexivity.

      (*KI_exchange*)
      inversion H; simpl in *; destruct (ktr s); try ve_pty_ua;
      try ve_pty_ua' H2 Heqktrs H0 IHHKI k0;
      try ve_pty_ua' H3 Heqktrs H0 IHHKI k0;
      try ve_pty_ua' H1 Heqktrs H0 IHHKI h0.
Qed.

Inductive auth_attempts : nat -> [KTrace] -> Prop :=
| naa_empty   : forall (n:nat), auth_attempts n [nil]%inhabited
| non_attempt : forall n tr act,
                  auth_attempts n [tr] ->
                  (forall c accstr, act <> KSend c (SysLoginReq accstr) )->
                  auth_attempts n [act :: tr]
| attempt     : forall c n tr accstr,
                  auth_attempts n [tr] ->
                  auth_attempts (S n) [KSend c (SysLoginReq accstr) :: tr].

Ltac ve_steps_att :=
  match goal with
  | [ IHHKI : auth_attempts _ (ktr ?s) |- auth_attempts _ (inhabit_unpack (ktr ?s)
                                                   (fun tr : KTrace =>
                                                    KSend _ (SysLoginReq _ _)
                                                          :: KRecv _ _ :: _))]
      => idtac "First"
  | [ IHHKI : auth_attempts _ (ktr ?s) |- auth_attempts _ (inhabit_unpack (ktr ?s)
                                                   (fun tr : KTrace =>
                                                    KSend _ _ :: KRecv _ _ :: _))]
      => destruct (ktr s);
         simpl;
         eapply non_attempt;
         [ eapply non_attempt; [apply IHHKI | discriminate]
         | discriminate]
  | [ IHHKI : auth_attempts _ (ktr ?s) |- auth_attempts _ (inhabit_unpack (ktr ?s)
                                                   (fun tr : KTrace =>
                                                    KRecv _ _ :: tr))]
      => destruct (ktr s);
         simpl;
         eapply non_attempt;
         [apply IHHKI | discriminate]
  end.

Lemma attempts_helper : forall st,
  KInvariant st -> auth_attempts (nat_of_num (logincnt st)) (ktr st).
Proof.
  intros st HKI.
  induction HKI; simpl in *.
    repeat econstructor; discriminate.

    destruct (ktr s).
    simpl.
    econstructor.
    apply IHHKI.
    discriminate.

    inversion H; simpl in *;
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      apply f_equal with (f:=logincnt) in H1;
      simpl in H1;
      rewrite H1;
      assumption
      | discriminate
      | discriminate]);
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      apply f_equal with (f:=logincnt) in H2;
      simpl in H2;
      rewrite H2;
      assumption
      | discriminate
      | discriminate]);
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      apply f_equal with (f:=logincnt) in H1;
      simpl in H1;
      rewrite H1;
      assumption
      | discriminate]);
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      apply f_equal with (f:=logincnt) in H0;
      simpl in H0;
      rewrite H0;
      assumption
      | discriminate]).

    destruct (ktr s).
    simpl in *.
    admit.
Qed.

Lemma logincnt_le_3 : forall st,
  KInvariant st -> nat_of_num (logincnt st) <= 3.
Proof.
  intros st HKI.
  induction HKI; simpl in *.
    auto.

    assumption.

    destruct H; simpl; try assumption.
      destruct IHHKI.
        destruct H.
        reflexivity.

        admit.
Qed.         
      
Theorem attempts_3 : forall st,
  KInvariant st -> auth_attempts 3 (ktr st).
Proof.
  intros st HKI.
  remember (ktr st) as ktrst.
  destruct ktrst.
  generalize dependent k.
  induction HKI; simpl in *; intros; rewrite Heqktrst; clear Heqktrst.
    (*KI_init*)
    repeat econstructor; discriminate.

    (*KI_select*)
    destruct ktr.
    simpl.
    econstructor.
    apply IHHKI.
    auto.
    discriminate.

    (*KI_exchange*)
    inversion H; simpl in *;
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      reflexivity |
      discriminate |
      discriminate]);
    try (destruct (ktr s);
      simpl in *;
      repeat econstructor;
      [apply IHHKI;
      reflexivity |
      discriminate]).
    remember (ktr s) as ktrs.
    destruct ktrs.
    simpl in *.
    apply attempt.
    apply non_attempt.
    rewrite Heqktrs.
    remember HKI as HKI'.
    clear HeqHKI'.
    apply logincnt_le_3 in HKI.
    inversion HKI.
    intuition.
    inversion H4.
    eapply attempts_helper.
    assumption.
    inversion H6.
Admitted.
          

