Require Import ActionMatch.
Require Import PolLang.
Require Import Reflex.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexBase.
Require Import Ynot.
Require Import List.
Require Import Decidable.

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

Ltac clear_useless_hyps :=
  repeat match goal with
         | [ H : _ = _ |- _ ]
           => revert H
         | [ H : _ <> _ |- _ ]
           => revert H
         | [ H : Reach _ _ _ _ _ |- _ ]
           => revert H
         | [ H : In _ _ |- _ ]
           => revert H
         | _
           => idtac
         end; clear; intros.

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

Lemma and_not_decide : forall P Q, decide P -> ~(P /\ Q) -> ~P \/ ~Q.
intros P Q dP H.
apply not_and in H.
auto.
unfold decidable; destruct dP; auto.
Qed.

Ltac get_decide P :=
  match P with
  | ?a = _ => match type of a with
             | str => apply str_eq
             | num => apply num_eq
             | fd => apply fd_eq
             end
  | _ => auto
  end.

Ltac destruct_neg_conjuncts H :=
  match type of H with
  | ~(?P /\ _) => let R := fresh "R" in
                  apply and_not_decide in H;
                  [ destruct H as [ | R ]; [ | destruct_neg_conjuncts R ] | get_decide P ]
  | _ => idtac
  end.

Ltac destruct_action_matches :=
  repeat match goal with
         | [ H : AMatch ?future ?act |- _ ]
           => compute in H (*maybe produces a conjunction of Props*);
              decompose [and] H
         | [ H : ~AMatch ?future ?act |- _ ]
           => compute in H
              (*maybe produces a negated conjunction of decidable Props*);
              destruct_neg_conjuncts H
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

Ltac impossible :=
  match goal with
  | [ H : ?x = _, H' : ?x = _ |- _ ]
      => rewrite -> H in H'; discriminate
  | [ H : _ = ?x, H' : _ = ?x |- _ ]
      => rewrite <- H in H'; discriminate
  end.

(********End General Tactics*********)

(********Begin Disable Tactics*********)

Ltac use_IH_disables :=
  match goal with
  | [ IHReach : context[forall tr' : KTrace, _],
      _ : ktr _ ?s = inhabits ?tr |- _ ]
      => apply IHReach with (tr':=tr); auto (*TODO: auto may not always work here.*)
  end.

(*This function should be passed a state. It will then attempt to prove
  that there are no instances of the disabler (should it be passed the disabler?)
  anywhere in the trace of that state.*)
(*There are two situations:
1.) The trace of the state is fully concrete: no induction required.
2.) The trace is not fully concrete: induction required.*)
Ltac forall_not_disabler s :=
  let t := type of s in
  match t with
  | kstate _ =>
     destruct_action_matches;
     (*Probably have to do something more intelligent than subst here.*)
     try subst;
     (*This may not clear the old induction hypothesis. Does it matter?*)
     clear_useless_hyps;
     (*Should this take s as an argument?*)
     reach_induction;
     match goal with
     | [ H : _ = initial_init_state _ _, H' : context[ In ?act _ ] |- _ ]
       => decompose [or] H';
          try solve [(subst act; tauto)
                    | contradiction
                    | discriminate
                    | impossible]
          (*subst act' works when it is set equal to actual action*)
          (*contradiction works when act' is in nil*)
          (*discriminate works when there is a
            contradiction with some property of the state*)
     | [ _ : ktr _ ?s' = inhabits _, H' : context[ In ?act _ ] |- _ ]
       => subst_assignments; subst_states; simpl in *;
          decompose [or] H';
          try solve [(subst act; tauto)
                    | discriminate
                    | contradiction
                    | use_IH_disables
                    | impossible
                    | forall_not_disabler s' ]
     end
  | _ => idtac "forall_not_disabler passed something which is not a kstate:" s t
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
  | [ _ : ktr _ ?s = inhabits _ |- Disables ?nb_msg ?pdv _ ?future (?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv future act) as H;
         destruct H;
         [ contradiction ||
           (apply D_disablee; [ match_disables | forall_not_disabler s])
         | contradiction ||
           (apply D_not_disablee; [ match_disables | assumption ]) ]
         (*In some cases, one branch is impossible, so contradiction
           solves the goal immediately.
           In other cases, there are variables in the message payloads,
           so both branches are possible.*)
  end.

(********End Disable Tactics********)

(********Begin Releases Tactics********)

Lemma cut_exists : forall nb_msg plt act disj_R conj_R,
  (exists past : @KAction nb_msg plt, (disj_R past) /\ (conj_R past)) ->
  exists past, (act = past \/ disj_R past) /\ (conj_R past).
Proof.
  intros nb_msg plt act disj_R conj_R H.
  destruct H.
  exists x.
  destruct H.
  auto.
Qed.

Ltac releaser_match :=
  simpl;
  match goal with
  | [ |- exists past : KAction, (?act = _ \/ ?disj_R ) /\ ?conj_R ]
    => (exists act; compute; tauto) ||
       (apply cut_exists; releaser_match)
  | _ => idtac
  end.

Ltac use_IH_releases :=
repeat match goal with
       | [ IHReach : context[ forall tr : KTrace, _ ] |- _ ]
         => apply IHReach; auto
       | _
         => apply cut_exists 
       end.

Ltac exists_past s :=
  let t := type of s in
  match t with
  | kstate _ =>
     destruct_action_matches;
     (*Probably have to do something more intelligent than subst here.*)
     subst_states;
     (*Try to match stuff at head of trace.*)
     releaser_match;
     (*This may not clear the old induction hypothesis. Does it matter?*)
     clear_useless_hyps;
     (*Should this take s as an argument?*)
     reach_induction;
     match goal with
     | [ H : _ = initial_init_state _ _ |- _ ]
       => try rewrite H in *;
          try solve [contradiction
                    | discriminate
                    | intuition
                    | impossible ]
          (*TODO: There may be the action we are looking for in this state.*)
     | [ _ : ktr _ ?s' = inhabits _ |- _ ]
       => subst_assignments; subst_states; repeat subst
          (*For any equalities generated by destructing the action match*);
          simpl in *;
          try solve [contradiction
                    | discriminate
                    | intuition
                    | impossible
                    | use_IH_releases
                    | releaser_match
                    | exists_past s']
          (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
     | _ => idtac
     end
  | _ => idtac "exists_past passed something which is not a kstate:" s t
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
  | [ _ : ktr _ ?s = inhabits _ |- Release ?nb_msg ?pdv _ ?future (?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv future act) as H;
         destruct H;
         [ contradiction ||
           (apply R_future; [ match_releases | exists_past s ])
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
