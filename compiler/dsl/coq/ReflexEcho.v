Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexIO.
Require Import ReflexVec.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("M", [str_d])
  ].

Notation M := 0%fin (only parsing).

Inductive COMPT' : Type := Echo1 | Echo2.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Echo1 => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  | Echo2 => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [].

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Echo1;
    Comp _ Echo2
  ].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq (spawn IENVD _ Echo1 tt None (Logic.eq_refl _))
  (seq (spawn IENVD _ Echo2 tt (Some None) (Logic.eq_refl _))
  nop).

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun m cc =>
    match m as _m return forall (EQ : _m = m), _ with
    | Build_msg None p => fun EQ =>
      let envd := existT _ 0 tt in
      existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc _ d) envd (
        let (msg, _) := p in
        seq (send envd _ _ ccomp None (mvar EQ None, tt))
        nop
      )
    | Build_msg (Some bad) _ =>
      match bad with end
    end (Logic.eq_refl m).

Require Import NonInterference.

Require Import Ynot.

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
  | [ m : msg _ |- _ ]
      => let tag := fresh "tag" in
         let pay := fresh "pay" in
         destruct m as [tag pay]; destruct_fin tag;
         destruct_pay pay
  end.

(*Destructs num, str, or fd equalities in the context.*)
Ltac destruct_eq H :=
  repeat match type of H with
         | context[if ?x then _ else _ ]
           => destruct x
         end.
 (* repeat match type of H with
         | context[num_eq ?a ?b]
           => destruct (num_eq a b); simpl in *
         | context[str_eq ?a ?b]
           => destruct (str_eq a b); simpl in *
         | context[fd_eq ?a ?b]
           => destruct (fd_eq a b); simpl in *
         end.*)

Ltac destruct_input input :=
  simpl in input; (*compute in input;*)
  match type of input with
  | unit => idtac
  | _ => let x := fresh "x" in
         let input' := fresh "input'" in
         destruct input as [x input']; destruct_input input'
  end.

Ltac unpack_inhabited :=
  repeat match goal with
         | [ H : ktr _ _ _ _ _ = inhabits ?tr |- _ ]
           => simpl in H; apply pack_injective in H; subst tr
         end.

Ltac unpack :=
  match goal with
  (*Valid exchange.*)
  | [ s : Reflex.kstate _ _ _ _, s' : Reflex.kstate _ _ _ _ |- _ ]
    => match goal with
       | [ _ : kstate_run_prog _ _ _ _ _ _ _ _ s _ = s' |- _ ]
         => subst s; subst s'
       end
  (*Initialization.*)
  | [ s : Reflex.init_state _ _ _ _ _ |- _ ]
    => match goal with
         | [ H : s = Reflex.init_state_run_cmd _ _ _ _ _ _ _ _ |- _ ]
           => subst s
       end
  (*Bogus msg*)
  end; unpack_inhabited.

Definition labeler (c : comp COMPT COMPS) :=
  match comp_type _ _ c with
  | Echo1 => true
  | Echo2 => false
  end.

Local Opaque str_of_string.

Ltac spawn_call :=
      match goal with
      | [ Hcall : call_ok _ _ _ _ _ _ |- call_ok _ _ _ _ _ _ ]
          => repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym in Hcall; try assumption;
             repeat apply call_ok_sub in Hcall; try assumption;
             apply call_ok_sym; try assumption
      | [ Hspawn : spawn_ok _ _ _ _ _ _ |- spawn_ok _ _ _ _ _ _ ]
          => repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym in Hspawn; try assumption;
             repeat apply spawn_ok_sub in Hspawn; try assumption;
             apply spawn_ok_sym; try assumption
      end.

Theorem ni : NIWeak' PAYD COMPT COMPTDEC COMPS IENVD KSTD INIT HANDLERS labeler.
Proof.
  apply ni_suf.
  unfold NonInterferenceSt'.
  intros.
  inversion H1.
  inversion H2.
  intros.
  destruct_msg.
  repeat unpack.
  simpl in *.
  rewrite H in *.
  inversion H7.
  f_equal; auto.
  apply H0; auto; try spawn_call.

  unfold NonInterferenceSt'.
  intros.
  inversion H1.
  destruct_msg.
  repeat unpack.
  simpl in *.
  rewrite H in *.
  apply H0; auto; try spawn_call.
Qed.
(*
unfold NIWeak'.
unfold NonInterference'.
  unfold NonInterferenceSt'.
  intros.
  generalize dependent tr1.
  generalize dependent tr2.
  generalize dependent s2.
  induction H; intros.
    induction H0.
      admit.

      inversion H6.
      destruct_msg.
      repeat unpack.
      simpl in *.
      destruct (labeler c).
        admit.
        admit.

      admit.

    inversion H0.
    destruct_msg.
    repeat unpack.
    simpl in *.
    destruct (labeler c).
      simpl in *.
      apply call_ok_sym in H4.
      repeat apply call_ok_sub in H4.
      apply spawn_ok_sym in H5.
      repeat apply spawn_ok_sub in H5.
      generalize dependent tr2.
      induction H1; intros.
        admit.

        inversion H2.
        destruct_msg.
        repeat unpack.
        simpl in *.
        destruct (labeler c0).
          inversion H6.
          replace a with a0 in * by admit.
          replace b with b0 in * by admit.
          f_equal; auto.
          apply IHReach with (s2:=s1); auto.
          admit.
          admit.

          apply IHReach0; auto.
          admit.
          admit.

        subst s'.
        simpl in *.
        apply pack_injective in H4.
        subst tr2.
        simpl in *.
        apply IHReach0; auto.
        admit.
        admit.

    apply IHReach with (s2:=s2); auto.
admit.
admit.

apply
  inversion H0.
  inversion H1.
  destruct_msg.
  repeat unpack.
  simpl in *.
  destruct (labeler c).
  
    

  apply H; eauto.
  apply call_ok_sym in H3; apply call_ok_sym;
  repeat apply call_ok_sub in H3; assumption.
  apply spawn_ok_sym in H4; apply spawn_ok_sym;
  repeat apply spawn_ok_sub in H4; assumption.
Qed.
*)
End Spec.

Module Main := MkMain(Spec).
Import Main.