Require Import ActionMatch.
Require Import PolLang.
Require Import Reflex.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexBase.
Require Import Ynot.
Require Import List.

(********Begin General Tactics*********)

Ltac destruct_fin f :=
  match type of f with
  | False => destruct f
  | _ => let f' := fresh "f" in
         destruct f as [ f' | ]; [destruct_fin f' | ]
  end.

Ltac destruct_pay pay :=
  compute in pay;
  match type of pay with
  | unit => idtac
  | _ => let a := fresh "a" in
         let b := fresh "b" in
         destruct pay as [a b]; simpl in a; destruct_pay b
  end.

Ltac destruct_msg :=
  match goal with
  | [ m : msg |- _ ]
      => let tag := fresh "tag" in
         let pay := fresh "pay" in
         destruct m as [tag pay]; destruct_fin tag;
         destruct_pay pay
  end.

(*Destructs num, str, or fd equalities in the context.*)
Ltac destruct_eq hdlrs H :=
  unfold hdlrs in H; simpl in H;
  match type of H with
  | context[num_eq ?a ?b]
    => destruct (num_eq a b); simpl in *; destruct_eq hdlrs H
  | context[str_eq ?a ?b]
    => destruct (str_eq a b); simpl in *; destruct_eq hdlrs H
  | context[fd_eq ?a ?b]
    => destruct (fd_eq a b); simpl in *; destruct_eq hdlrs H
  | _
    => idtac
  end.

Ltac unpack :=
  match goal with
  | [ H : ?s = _, H' : ?s' = kstate_run_prog ?KST_DESC _ _ _ ?s _ |- _ ]
      => rewrite H in H'; rewrite H' in *; simpl in *; unpack
  | [ s : init_state _ _ |- _ ]
      => match goal with
         | [ H : s = _ |- _ ]
             => rewrite H in *; simpl in *; unpack
         end
  | [ tr : KTrace |- _ ]
      => match goal with
         | [ H: [_]%inhabited = [tr]%inhabited |- _ ]
             => apply pack_injective in H; subst tr
         | [ H: [tr]%inhabited = [_]%inhabited |- _ ]
             => apply pack_injective in H; subst tr
         end
  end.

(*Erases hypothesis relating to old states on which we are not performing induction.*)
(*First rewrites those states to avoid losing information.*)
Ltac clear_old_hyps :=
  match goal with
  | [ s : kstate _, s' : kstate _ |- _ ]
      => match goal with
         | [ H : s = _, H' : s' = _,
             IHReach : forall tr : KTrace, _ |- _ ]
           => subst s; subst s'; clear IHReach
         end
  end.

Ltac destruct_unpack :=
  match goal with
  | [ m : msg, H : _ = kstate_run_prog _ _ _ _ _ _,
      H' : Reach _ _ _ ?HDLRS _ |- _ ]
      => destruct_msg; destruct_eq HDLRS H; unpack
  | [ m : msg |- _ ]
      => destruct_msg; unpack
  | _
      => unpack
  end.

Ltac subst_states :=
  match goal with 
  | [ s : kstate _ |- _ ]
      => match goal with
         | [ _ : s = _ |- _ ]
             => subst s; subst_states
         end
  | _
      => idtac
  end.

Ltac subst_assignments :=
  match goal with
  | [ a := _ |- _ ]
      => subst a; subst_assignments
  | _
      => idtac
  end.

Ltac destruct_conjuncts H :=
  match type of H with
  | _ /\ _ => let L := fresh "L" in
              let R := fresh "R" in
              destruct H as [L R]; destruct_conjuncts R
  | _ => idtac
  end.

Ltac destruct_disjuncts H :=
  match type of H with
  | _ \/ _ => let L := fresh "L" in
              let R := fresh "R" in
              destruct H as [L | R]; destruct_disjuncts R
  | _ => idtac
  end.

Ltac destruct_action_match :=
  match goal with
  | [ H : AMatch ?future ?act |- _ ]
      => compute in H (*produces a conjunction of Props*);
         destruct_conjuncts H
  end.

Ltac act_match :=
  match goal with
  | [ |- @AMatch ?nb_msg ?pdv ?oact ?act ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact act) as H;
         destruct H; [ assumption | contradiction ]
  end.

Ltac act_nmatch :=
  match goal with
  | [ |- ~@AMatch ?nb_msg ?pdv ?oact ?act ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact act) as H;
         destruct H; [ contradiction | assumption ]
  end.

Ltac msg_fds_are_ok :=
  match goal with
  | [ H : ~msg_fds_ok _ _ _ |- _ ]
      => contradict H; compute; msg_fds_are_ok
  | [ |- forall i : _, _ ]
      => intro i; destruct_fin i; contradiction || auto
  end.

Ltac reach_induction :=
  intros;
  match goal with
  | [ _ : ktr _ _ = inhabits ?tr, H : Reach _ _ _ _ _ |- _ ]
      => generalize dependent tr; induction H;
         simpl in *; intros; destruct_unpack;
         try msg_fds_are_ok
         (*msg_fds_are_ok eliminates bad fds case when that's impossible.*)
  end.

(********End General Tactics*********)

(********Begin Disable Tactics*********)

Ltac use_IH_disables :=
  match goal with
  | [ IHReach : context[forall tr' : KTrace, ktr _ ?s = inhabits tr' -> _],
      _ : ktr _ ?s = inhabits ?tr |- _ ]
      => let act := fresh "act" in
         let H'' := fresh "H" in
         apply IHReach with (tr':=tr); auto (*TODO: auto may not always work here.*)
  end.
(*This function should be passed a state. It will then attempt to prove
  that there are no instances of the disabler (should it be passed the disabler?)
  anywhere in the trace of that state.*)
(*There are two situations:
1.) The trace of the state is fully concrete: no induction required.
2.) The trace is not fully concrete: induction required.*)
Ltac forall_not_disabler :=
  let HIn := fresh "HIn" in
  let act' := fresh "act'" in
  (*Checks the concrete actions at the head of the trace.*)
  intros act' HIn; simpl in HIn; destruct_disjuncts HIn;
  try (subst act'; simpl; tauto);
  destruct_action_match;
  clear_old_hyps;
  reach_induction;
  match goal with
  | [ H : _ = initial_init_state _ _, H' : context[ In _ _ ] |- _ ]
      => destruct_disjuncts H'; (subst act'; tauto) || contradiction
         (*subst act' works when it is set equal to actual action*)
         (*contradiction works when act' is in nil*)
  | [ H' : context[ In _ _ ] |- _ ]
      => subst_assignments; subst_states; simpl in *;
         destruct_disjuncts H';
         try solve [(subst act'; tauto) | discriminate | use_IH_disables]
  end.

Ltac match_disables :=
  match goal with
  | [ |- Disables _ _ _ _ nil ]
      => constructor
  (* Induction hypothesis.*)
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', ktr _ ?s = inhabits tr' ->
                       Disables _ _ ?past ?future tr'
                       |- Disables _ _ ?past ?future ?tr ]
      => auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Disables ?nb_msg ?pdv _ ?future (?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv future act) as H;
         destruct H;
         [ contradiction ||
           (apply D_disablee; [ match_disables | forall_not_disabler ])
         | contradiction ||
           (apply D_not_disablee; [ match_disables | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

(********End Disable Tactics********)

(********Begin Releases Tactics********)

(*Should only be called by releaser_match.*)
Ltac releaser_match' :=
  match goal with
  | [ |- (?act = _ \/ ?disj_R ) /\ ?conj_R ]
    => (instantiate (1:=act); compute; tauto) ||
       (cut (disj_R /\ conj_R); [ | releaser_match']; tauto)
       (*The last call to tauto solves the first goal created by cut.
         However, it can't solve this goal until the existential variable
         is instantiated, which happens in the recursive call to releaser_match'.*)
  | _ => fail 1
  end.

Ltac releaser_match :=
  eexists; releaser_match'.

Ltac use_IH_releases :=
  match goal with
  | [ IHReach : ?H -> ?rest, H' : ?H, _ : ktr _ ?s = inhabits ?tr |- _ ]
    => match rest with
       | context[forall tr' : KTrace, ktr _ s = inhabits tr' -> _]
          => let act := fresh "act" in
             let H'' := fresh "H" in
             apply IHReach with (tr':=tr) in H'; auto;
             (*TODO: What if there is more than one hypothesis?*)
             destruct H' as [ act H'' ]; exists act; tauto
       end
  end.

(*TODO: Do we check the actions at the head of the trace? Maybe...*)
Ltac exists_past :=
  destruct_action_match;
  clear_old_hyps;
  reach_induction;
  match goal with
  | [ H : _ = initial_init_state _ _ |- _ ]
      => rewrite H in *; intuition (*Initial state. Contradiction?*)
         (*TODO: There may be the action we are looking for in this state.*)
  | _
      => subst_assignments; subst_states; repeat subst
         (*For any equalities generated by destructing the action match*);
         simpl in *;
         try solve [contradiction | use_IH_releases | releaser_match]
         (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
  end.

Ltac match_releases :=
  match goal with
  | [ |- Release _ _ _ _ nil ]
      => constructor
  (* Induction hypothesis.*)
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', ktr _ ?s = inhabits tr' ->
                       Release _ _ ?past ?future tr'
                       |- Release _ _ ?past ?future ?tr ]
      => auto
  (*Branch on whether the head of the trace matches.*)
  | [ |- Release ?nb_msg ?pdv _ ?future (?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv future act) as H;
         destruct H;
         [ contradiction ||
           (apply R_future; [ match_releases | exists_past ])
         | contradiction ||
           (apply R_not_future; [ match_releases | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

(********End Releases Tactics********)

(*******Begin Immediately Before Tactics********)

Ltac match_immbefore := 
  match goal with
  | [ |- ImmBefore _ _ _ _ nil ]
      => constructor
  (*Induction hypothesis*)
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', ktr _ ?s = inhabits tr' ->
                       ImmBefore _ _ ?oact_b ?oact_a tr'
                       |- ImmBefore _ _ ?oact_b ?oact_a ?tr ]
      => auto
  | [ |- ImmBefore ?nb_msg ?pdv _ ?oact_a (?act::_) ]
     => let H := fresh "H" in
        pose proof (decide_act nb_msg pdv oact_a act) as H;
        destruct H;
        [ contradiction ||
          (apply IB_A; [ match_immbefore | act_match ])
        | contradiction ||
          (apply IB_nA; [ match_immbefore | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

(*******End Immediately Before Tactics********)

(*******Begin Immediately After Tactics********)

Ltac match_immafter := 
  match goal with
  | [ |- ImmAfter _ _ _ _ nil ]
      => constructor
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', ktr _ ?s = inhabits tr' ->
                       ImmAfter _ _ ?oact_a ?oact_b tr'
                       |- ImmAfter _ _ ?oact_a ?oact_b ?tr ]
      => auto
  | [ |- ImmAfter ?nb_msg ?pdv _ ?oact_b (_::?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv oact_b act) as H;
         destruct H;
         [ contradiction ||
           (apply IA_B; [ match_immafter | act_match ] )
         | contradiction ||
           (apply IA_nB; [ match_immafter | act_nmatch ] ) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  | [ |- ImmAfter _ _ _ _ (?act::_) ]
      (*If theres only one concrete action at the head of the trace,
        it better not a before action because there's nothing after.*)
      => apply IA_nB; [ match_immafter | act_nmatch ]
  end.

(*******End Immediately After Tactics********)

(*******Main Tactic******)

Ltac crush :=
  reach_induction;
  match goal with
  | [ |- ImmBefore _ _ _ _ _ ]
     => match_immbefore
  | [ |- ImmAfter _ _ _ _ _ ]
     => match_immafter
  | [ |- Disables _ _ _ _ _ ]
     => match_disables
  | [ |- Release _ _ _ _ _ ]
     => match_releases
  end.
