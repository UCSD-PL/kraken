Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.

Definition NB_MSG : nat := 2.

Definition PAY_DESC : vvdesc NB_MSG :=
  ( existT _ 1 (str_d, tt) (*User name payload.*)
   , ( existT _ 2 (str_d, (num_d, tt)) (*Auth response from system payload.*)
    , tt)
  ).

Definition INIT_ENVD : vdesc := existT _ 0 tt.

Definition KST_DESC_SIZE := 2.

(*State is (username, authres)*)
Definition KST_DESC : vdesc' KST_DESC_SIZE := (str_d, (num_d, tt)).

Definition INIT : @init_prog NB_MSG PAY_DESC _ KST_DESC INIT_ENVD :=
  nil.

Definition HANDLERS : handlers (VVD := PAY_DESC) KST_DESC :=
  (fun m f st =>
    match tag m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag (VVD := PAY_DESC) _tm) -> _
    with
    | None => fun pl =>
       let (u, _) := pl in
       let envd := existT _ 0 tt in
       if num_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) (Some None))
                    (num_of_nat 0)
       then existT _ envd (nil) (*Ignore.*)
       else if str_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None)
                    u
            then existT _ envd (
                          let (u, _) := pl in
                          Send _ _ _
                               (HEchan _ _)
                               (@MEmsg _ PAY_DESC envd None (SLit _ u, tt))
                               :: nil
                          )
            else existT _ envd (nil) (*Ignore.*)
       (*match str_eq (@shvec_ith _ _ _
                                (KST_DESC:svec desc KST_DESC_SIZE)
                                (kst _ st) None)
                    u*)
       (*with
       | left _ => existT _ envd (nil) (*Ignore.*)
       | right _ => existT _ envd (
                             let (u, _) := pl in
                             Send _ _ _
                                  (HEchan _ _)
                                  (@MEmsg _ PAY_DESC envd None (SLit _ u, tt))
                             :: nil
                           )
       end*)
    | Some None => fun pl =>
       let envd := existT _ 0 tt in
       existT _ envd (
        let (u, pl') := pl in
        let (res, _) := pl' in
        STChange KST_DESC _ _
          None (HEexpr _ _ _ (MEbase _ _ (SLit _ u)))
        :: STChange KST_DESC _ _
             (Some None) (HEexpr _ _ _ (MEbase _ _ (NLit _ res)))
        :: nil
      )
    | Some (Some bad) => fun _ =>
      match bad with end
    end (pay m)
  ).

Require Import PolLang.
Require Import ActionMatch.
Require Import Tactics.
Require Import ReflexFin.
Require Import List.

Ltac destruct_msg :=
  match goal with
  (*Tag is Some False*)
  | [ f : False |- _ ]
      => destruct f
  | [ pay : s[[lkup_tag (Some ?f)]] |- _ ]
      => match type of f with
         | option _ => destruct f; destruct_msg
         end
  | [ pay : s[[lkup_tag _]] |- _ ]
      => destruct pay; simpl in *; destruct_msg
  | [ a : prod _ _ |- _ ]
      => destruct a; simpl in *; destruct_msg
  | [ tag : fin _ |- _ ]
      => destruct tag; destruct_msg
  | [ m : msg |- _ ]
      => destruct m; destruct_msg
  | _
    => idtac
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

Require Import Ynot.
    Ltac unpack :=
  match goal with
  | [ s : kstate _, H : ?s = _, s' : kstate _,
      H' : ?s' = kstate_run_prog ?KST_DESC _ _ _ ?s _ |- _ ]
      => rewrite H in H'; rewrite H' in *; simpl in *; unpack
  | [ s : init_state _ _, H : ?s = _ |- _ ]
      (*This is problematic because it destroys information about s*)
      => rewrite H in *; simpl in *; unpack
  | [ H: [_]%inhabited = [_]%inhabited |- _ ]
      => apply pack_injective in H;
         rewrite -> H || rewrite <- H
  end.

(*Erases hypothesis relating to old states on which we are not performing induction.*)
(*First rewrites those states to avoid losing information.*)
Ltac clear_old_hyps :=
  match goal with
  | [ s : kstate _, s' : kstate _, tr : KTrace |- _ ]
      => match goal with
         | [ H : s = _, H' : s' = _, H'' : tr = _,
             IHReach : forall tr : KTrace, _ |- _ ]
           => try rewrite H in *; try rewrite H' in *;
              clear dependent s; clear dependent s';
              clear dependent tr; clear IHReach
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

Ltac use_IH :=
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

Ltac releaser_match :=
    match goal with
    | [ |- context[ In _ (?act::_) ] ]
      => exists act; compute; tauto
    | [ |- context[ In _ (_::?act::_) ] ]
      => exists act; compute; tauto
    | [ |- context[ In _ (_::_::?act::_) ] ]
      => exists act; compute; tauto
    | [ |- exists past, (?act = past \/ _ ) /\ _ ]
      => exists act; compute; tauto
    | [ |- exists past, (_ \/ ?act = past \/ _ ) /\ _ ]
      => exists act; compute; tauto
    | [ |- exists past, (_ \/ _ \/ ?act = past \/ _ ) /\ _ ]
      => exists act; compute; tauto
    | [ |- exists past, (_ \/ _ \/ _ \/ ?act = past \/ _ ) /\ _ ]
      => exists act; compute; tauto
    end.

Ltac destruct_conjuncts H :=
  match type of H with
  | _ /\ _ => let L := fresh "L" in
              let R := fresh "R" in
              destruct H as [L R]; destruct_conjuncts R
  | _ => idtac
  end.

Ltac destruct_action_match :=
  match goal with
  | [ H : AMatch ?future ?act |- _ ]
      => compute in H (*produces a conjunction of Props*);
         let L := fresh "L" in
         let R := fresh "R" in
         destruct H as [L R]; destruct_conjuncts R
  end.

Ltac exists_past :=
  destruct_action_match;
  clear_old_hyps;
  match goal with
  | [ _ : ktr _ _ = inhabits ?tr, H : Reach _ _ _ _ _ |- _ ]
      => generalize dependent tr; induction H; simpl in *; intros
  end;
  match goal with
  | [ H : _ = initial_init_state _ _ |- _ ]
      => rewrite H in *; intuition (*Initial state. Contradiction?*)
  | _
      => destruct_unpack; subst_assignments; subst_states;
         try subst (*For any equalities generated by destructing the action match*);
         simpl in *; try contradiction; try releaser_match; try use_IH
         (*destruct_eq might have created contradictions
           with previous calls of destruct_eq*)
  end.

Ltac match_releases :=
  match goal with
  | [ |- Release _ _ _ _ nil ]
      => constructor
  | [ H : ktr _ ?s = inhabits ?tr,
      IH : forall tr', inhabits tr' = ktr _ ?s ->
                       Release _ _ ?past ?future tr'
                       |- Release _ _ ?past ?future ?tr ]
      => auto
  | [ H : AMatch ?future ?act |- Release ?nb_msg ?pdv _ ?future (?act::_) ]
      => apply R_future; [ match_releases | exists_past ]
  | [ H : ~AMatch ?future ?act |- Release ?nb_msg ?pdv _ ?future (?act::_) ]
      => apply R_not_future; [ match_releases | assumption ]
  | [ |- Release ?nb_msg ?pdv _ ?future (?act::_) ]
      => let H := fresh "H" in
         pose proof (decide_act nb_msg pdv future act) as H;
         destruct H; try contradiction; match_releases
  end.

Theorem release : forall st tr u,
  Reach _ _ INIT HANDLERS st -> inhabits tr = ktr _ st ->
  Release NB_MSG PAY_DESC
          (@KORecv NB_MSG PAY_DESC None
                   (Some (@Build_opt_msg NB_MSG PAY_DESC
                                         (Some None) (Some u, (None, tt)))))
          (@KOSend NB_MSG PAY_DESC None
                   (Some (@Build_opt_msg NB_MSG PAY_DESC
                                         None (Some u, tt))))
          tr.
Proof.
  intros.
  generalize dependent tr.
  induction H; simpl in *; intros;
  destruct_unpack; match_releases.
Qed.

Theorem release_exists : forall st tr u,
  Reach _ _ INIT HANDLERS st -> inhabits tr = ktr _ st ->
  (exists n, n > 0 /\
              Release NB_MSG PAY_DESC
                      (@KORecv NB_MSG PAY_DESC None
                               (Some (@Build_opt_msg NB_MSG PAY_DESC
                                       (Some None) (Some u, (Some (num_of_nat n), tt)))))
                      (@KOSend NB_MSG PAY_DESC None
                               (Some (@Build_opt_msg NB_MSG PAY_DESC
                                       None (Some u, tt))))
          tr).
Admitted.