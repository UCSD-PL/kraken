Require Import ReflexEcho.
Require Import RegexTacs.
Require Import RegexProof.
Require Import RegexNoInd.
Require Import PolLang.
Require Import Reflex.
Require Import ReflexEcho.

Ltac act_match :=
  match goal with
  | [ |- @AMatch ?nb_msg ?pdv ?oact ?act ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact act) as H;
         destruct H; [ assumption | contradiction ]
  end.

Ltac match_immbefore := 
  match goal with
  | [ |- ImmBefore _ _ _ _ nil ]
      => constructor
  (*Induction hypothesis*)
  | [ H : ktr ?s = inhabits ?tr,
      IH : forall tr', inhabits tr' = ktr ?s ->
                       ImmBefore _ _ ?oact_b ?oact_a tr'
                       |- ImmBefore _ _ ?oact_b ?oact_a ?tr ]
      => auto
  | [ H : AMatch ?oact_a ?act |- ImmBefore _ _ _ ?oact_a (?act::_::_) ]
      => apply IB_A; [ match_immbefore | act_match ]
  | [ H : AMatch ?oact_a ?act |- ImmBefore _ _ _ ?oact_a (?act::_) ]
      => contradiction
  | [ H : ~ AMatch ?oact_a ?act |- ImmBefore _ _ _ ?oact_a (?act::_) ]
      => apply IB_nA; [ match_immbefore | assumption ]
  | [ |- ImmBefore ?nb_msg ?pdv _ ?oact_a (?act::_) ]
     => let H := fresh "H" in
        pose proof (decide_act nb_msg pdv oact_a act) as H;
        destruct H; match_immbefore
  end.

Ltac act_nmatch :=
  match goal with
  | [ |- ~@AMatch ?nb_msg ?pdv ?oact ?act ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact act) as H;
         destruct H; [ contradiction | assumption ]
  end.

Ltac match_immafter := 
  match goal with
  | [ |- ImmAfter _ _ _ _ nil ]
      => constructor
  | [ H : ktr ?s = inhabits ?tr,
      IH : forall tr', inhabits tr' = ktr ?s ->
                       ImmAfter _ _ ?oact_a ?oact_b tr'
                       |- ImmAfter _ _ ?oact_a ?oact_b ?tr ]
      => auto
  | [ H : AMatch ?oact_b ?act |- ImmAfter ?nb_msg ?pdv _ ?oact_b (_::?act::_) ]
      => apply IA_B; [ match_immafter | act_match ] || idtac
  | [ H : ~AMatch ?oact_b ?act |- ImmAfter ?nb_msg ?pdv _ ?oact_b (_::?act::_) ]
      => apply IA_nB; [ match_immafter | act_nmatch ] || idtac
  | [ |- ImmAfter ?nb_msg ?pdv _ ?oact_b (_::?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact_b act) as H;
         destruct H; match_immafter
  | [ |- ImmAfter _ _ _ _ (?act::_) ]
      => apply IA_nB; [ match_immafter | act_nmatch ]
  end.

Ltac msg_fds_are_ok :=
  match goal with
  | [ H : ~msg_fds_ok _ _ |- _ ]
      => contradict H; compute; msg_fds_are_ok
  | [ |- forall i : _, _ ]
      => intro i; destruct i; contradiction || auto
  end.

Ltac crush :=
  match goal with
  | [ m : msg |- _ ]
      => destruct_msg; crush
  | [ |- ImmBefore _ _ _ _ _ ]
      => unpack; solve [match_immbefore]
  | [ |- ImmAfter _ _ _ _ _ ]
      => unpack; solve [match_immafter]
  | [ H : ~ msg_fds_ok _ _ |- _ ]
      => msg_fds_are_ok
  end.

Theorem recv_before : forall st tr m,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  ImmBefore NB_MSG PDV
            (@KORecv NB_MSG PDV None
                     (Some (@Build_opt_msg NB_MSG PDV
                                           None (Some m, tt))))
            (@KOSend NB_MSG PDV None
                     (Some (@Build_opt_msg NB_MSG PDV
                                           None (Some m, tt))))
            tr.
Proof.
  intros.
  generalize dependent tr.
  induction H; simpl in *; intros;
  crush.
Qed.

Theorem send_after : forall st tr m,
  Reach HANDLERS st -> inhabits tr = ktr st ->
  ImmAfter NB_MSG PDV
            (@KOSend NB_MSG PDV None
                     (Some (@Build_opt_msg NB_MSG PDV
                                           None (Some m, tt))))
            (@KORecv NB_MSG PDV None
                     (Some (@Build_opt_msg NB_MSG PDV
                                           None (Some m, tt))))
            tr.
Proof.
  intros.
  generalize dependent tr.
  induction H; simpl in *; intros;
  crush.
Qed.