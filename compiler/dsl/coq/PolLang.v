Require Import Reflex.
Require Import ReflexBase.
Require Import ActionMatch.
Require Import List.

Section PolLang.

Context {NB_MSG:nat}.
Variable PAYD:vvdesc NB_MSG.
Variable COMPT : Set.
Variable COMPS : COMPT -> compd.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Definition KOAction := KOAction PAYD COMPT COMPS.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition AMatch := AMatch PAYD COMPT COMPS COMPTDEC.

(*after occurs immediately after before occurs.*)
Inductive ImmAfter (after:KOAction) (before:KOAction)
  : KTrace -> Prop :=
| IA_nil : ImmAfter after before nil
(*An action not matching before is added*)
| IA_nB : forall before' tr, ImmAfter after before tr ->
                             ~AMatch before before' ->
                             ImmAfter after before (before'::tr)
(*An action matching before is added*)
| IA_B : forall before' after' tr, ImmAfter after before tr ->
                                   AMatch after after' ->
                                   ImmAfter after before (after'::before'::tr).

(*before occurs immediate before after occurs*)
Inductive ImmBefore (before:KOAction) (after:KOAction)
  : KTrace -> Prop :=
| IB_nil : ImmBefore before after nil
(*An action not matching after is added*)
| IB_nA : forall after' tr, ImmBefore before after tr ->
                            ~AMatch after after' ->
                            ImmBefore before after (after'::tr)
(*An action matching after is added*)
| IB_A : forall after' before' tr, ImmBefore before after tr ->
                                   AMatch before before' ->
                                   ImmBefore before after (after'::before'::tr).

Inductive Enables (past:KOAction) (future:KOAction)
  : KTrace -> Prop :=
| E_nil : Enables past future nil
| E_not_future : forall act tr, Enables past future tr ->
                                ~AMatch future act ->
                                Enables past future (act::tr)
| E_future : forall act tr, Enables past future tr ->
                            (exists past', In past' (act::tr) /\
                                           AMatch past past') ->
                            Enables past future (act::tr).

Definition Not_In (A:KOAction) (tr:KTrace) : Prop :=
  forall a, In a tr -> ~AMatch A a.

Inductive Enables' (past:KOAction) (future:KOAction)
  : KTrace -> Prop :=
| E_not_A_B : forall tr, Not_In past tr -> Not_In future tr ->
                         Enables' past future tr
| E_A : forall tr tr' a, Not_In future tr ->
                         AMatch past a ->
                         Enables' past future (tr' ++ a::tr).

Lemma not_in_cons : forall A x tr,
  Not_In A (x::tr) -> Not_In A tr.
Proof.
  intros A x tr HNot_In.
  unfold Not_In in *.
  intros a HIn.
  pose proof (HNot_In a) as H.
  apply H.
  simpl; right; assumption.
Qed.  

Theorem enables_equiv : forall A B tr,
  Enables A B tr <-> Enables' A B tr.
Proof.
  intros A B tr.
  split.
    (*Enables -> Enables'*)
    intro E.
    induction E.
      apply E_not_A_B; unfold Not_In; intros a HIn; auto.

      inversion IHE.
        pose proof (decide_act PAYD COMPT COMPS COMPTDEC A act) as Hact;
        destruct Hact.
          (*act matches A*)
          replace (act::tr) with (nil++act::tr) by auto;
          apply E_A; auto.

          (*act does not match A*)
          apply E_not_A_B; unfold Not_In in *; intros a HIn;
          simpl in HIn; destruct HIn; (subst a; auto) || auto.

        replace (act::tr'++a::tr0) with ((act::tr')++a::tr0) by auto;
        apply E_A; auto.

      inversion IHE.
        unfold Not_In in H0; destruct H; pose proof (H0 x);
        simpl in H; destruct H as [HL HR]; destruct HL.
          replace (act :: tr) with (nil ++ act :: tr) by auto;
          subst act; apply E_A; auto.

          tauto.

        replace (act::tr'++a::tr0) with ((act::tr')++a::tr0) by auto;
        apply E_A; auto.
    
    (*Enables' -> Enables*)
    intro E'.
    destruct E'.
      induction tr.
        apply E_nil.
        
        apply E_not_future.
        apply IHtr; eapply not_in_cons; eauto.

        unfold Not_In in H0.
        pose proof (H0 a) as H'.
        simpl in H'.
        auto.

      induction tr'.
        induction tr.
          simpl.
          apply E_future.
            apply E_nil.
            
            exists a; simpl; auto.

          simpl in *.
          remember H as H'; clear HeqH'.
          apply not_in_cons in H.
          apply IHtr in H.
          inversion H.
            apply E_future.
              apply E_not_future.
                assumption.
 
                unfold Not_In in H'.
                pose proof (H' a0).
                intuition.

              exists a; intuition.

            destruct H4; destruct H4; simpl in H4; destruct H4.
              subst x.
              apply E_future.
                apply E_not_future.
                  assumption.
 
                  unfold Not_In in H'.
                  pose proof (H' a0).
                  intuition.

                exists a; intuition.

              repeat apply E_future; auto || (exists x; intuition).

          replace ((a0 :: tr') ++ a :: tr) with (a0 :: (tr' ++ a :: tr)) by auto.
          apply E_future.
            assumption.

            exists a; intuition.
Qed.        

Inductive Disables (disabler:KOAction) (disablee:KOAction)
  : KTrace -> Prop :=
| D_nil : Disables disabler disablee nil
| D_not_disablee : forall act tr, Disables disabler disablee tr ->
                                  ~AMatch disablee act ->
                                  Disables disabler disablee (act::tr)
| D_disablee : forall act tr, Disables disabler disablee tr ->
                              (forall act', In act' tr ->
                                            ~AMatch disabler act') ->
                              Disables disabler disablee (act::tr).

End PolLang.
