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
  seq (spawn _ IENVD Echo1 tt None (Logic.eq_refl _))
  (seq (spawn _ IENVD Echo2 tt (Some None) (Logic.eq_refl _))
  nop).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | None, _ =>
    [[ mk_vcdesc [] :
       send ccomp None (mvar None None, tt) ]]
  | Some bad, _ =>
    match bad with end
  end.
Close Scope hdlr.

Require Import NonInterference.

Require Import Ynot.
Require Import NITactics.

Definition clblr (c : comp COMPT COMPS) :=
  match comp_type _ _ c with
  | Echo1 => true
  | Echo2 => false
  end.

Definition vlblr (f : fin (projT1 KSTD)) : bool :=
  match f with end.

Theorem ni : NonInterference PAYD COMPT COMPTDEC COMPS
                             IENVD KSTD INIT HANDLERS
                             (nd_strong PAYD COMPT COMPS) clblr vlblr.
Proof.
  apply ni_suf.
Ltac high_steps :=
  intros;
  match goal with
  | [ IH : NonInterferenceSt _ _ _ _ _ _ _ _ _ _ |- _ ]
    => unfold NonInterferenceSt in *; intros;
       match goal with
       | [ Hve1 : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hve2 : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hins : inputs _ _ _ _ _ = inputs _ _ _ _ _,
           Hhigh : _ _ = true |- _ ]
         => inversion Hve1; inversion Hve2;
            destruct_msg; destruct_comp; repeat unpack;
             simpl in *; rewrite Hhigh in *; inversion Hins;
            split; [f_equal; auto; apply IH; auto; try spawn_call | ]
       end
  end.
high_steps.
Set Ltac Debug.
match goal with
|- vars_eq _ _ _ _ _ ?s1' ?s2' _ = true
  => rewrite vars_eq_kst with (s1':=s1') (s2':=s2')
end.
rewrite vars_eq_kst. vars_eq_kst. apply H0; auto; try spawn_call.

Ltac low_step :=
  intros;
  match goal with
  | [ IH : NonInterferenceSt _ _ _ _ _ _ _ _ |- _ ]
    => unfold NonInterferenceSt in *; intros;
       match goal with
       | [ Hve : ValidExchange _ _ _ _ _ _ _ _ _ _,
           Hlow : _ _ = false |- _ ]
         => inversion Hve; destruct_msg; destruct_comp; repeat unpack;
            simpl in *; rewrite Hlow in *; apply IH; auto; try spawn_call
       end
  end.
  ni.
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
