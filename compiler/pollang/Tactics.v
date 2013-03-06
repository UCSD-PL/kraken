Require Import ActionMatch.
Require Import PolLang.
Require Import Reflex.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import Ynot.

Ltac unpack :=
  match goal with
  | [ s : kstate _, H : ?s = _,
      s' : kstate _, H' : ?s' = kstate_run_prog ?KST_DESC _ _ _ ?s _ |- _ ]
      => rewrite H in H'; apply f_equal with (f:=ktr KST_DESC) in H';
         simpl in H'; rewrite H' in *; unpack
  | [ s : init_state _ _, H : ?s = _ |- _ ]
      (*This is problematic because it destroys information about s*)
      => rewrite H in *; simpl in *; unpack
  | [ H: [_]%inhabited = [_]%inhabited |- _ ]
      => apply pack_injective in H;
         rewrite -> H in * || rewrite <- H in *
  end.

Ltac destruct_msg :=
  match goal with
  (*Tag is Some False*)
  | [ f : False |- _ ]
      => destruct f
  | [ f : option _, pay : s[[lkup_tag (Some ?f)]] |- _ ]
      => destruct f; destruct_msg
  | [ pay : s[[lkup_tag _]] |- _ ]
      => destruct pay; simpl in *
  | [ tag : fin _ |- _ ]
      => destruct tag; destruct_msg
  | [ m : msg |- _ ]
      => destruct m; destruct_msg
  end.

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
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', inhabits tr' = ktr _ ?s ->
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
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', inhabits tr' = ktr _ ?s ->
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
  | [ H : ~msg_fds_ok _ _ _ |- _ ]
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
  | [ H : ~ msg_fds_ok _ _ _ |- _ ]
      => msg_fds_are_ok
  end.