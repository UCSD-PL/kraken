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
Hint Unfold AMatch.

(*B occurs immediately after A occurs.*)
(*Inductive ImmAfter (B:KOAction) (A:KOAction)
  : KTrace -> Prop :=
| IA_nil : ImmAfter B A nil
| IA_single : forall x, ImmAfter B A (x::nil)
| IA_B : forall b tr, ImmAfter B A tr ->
                      AMatch B b ->
                      ImmAfter B A (b::tr)
| IA_nA : forall x na tr, ImmAfter B A (na::tr) ->
                          ~AMatch A na ->
                          ImmAfter B A (x::na::tr).*)

(*A immediate before B occurs*)
Inductive ImmBefore (A:KOAction) (B:KOAction)
  : KTrace -> Prop :=
| IB_nil : ImmBefore A B nil
| IB_nB : forall nb tr, ImmBefore A B tr ->
                        ~AMatch B nb ->
                        ImmBefore A B (nb::tr)
| IB_A : forall x a tr, ImmBefore A B (a::tr) ->
                        AMatch A a ->
                        ImmBefore A B (x::a::tr).

Theorem immbefore_ok :
  forall A B b T1 T2,
    AMatch B b ->
    ImmBefore A B (T1 ++ b::T2) ->
    exists a, exists T3,
      AMatch A a /\ T2 = a::T3.
Proof.
  intros A B b T1 T2 HmatchB Hib.
  remember (T1 ++ b::T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction Hib; intros T2 T1 HT.
    pose (app_cons_not_nil T1 T2 b).
    contradiction.

    destruct T1.
      simpl in HT. inversion HT.
      subst b. contradiction.

      inversion HT. eauto.

    destruct T1.
      simpl in HT. inversion HT. eauto.

      inversion HT. eauto.
Qed.

Definition ImmAfter B A tr := ImmBefore B A (rev tr).

Lemma immafter_ok :
  forall A B a T1 T2,
  AMatch A a ->
  ImmAfter B A (T1 ++ a::T2) ->
  exists b, exists T3,
    AMatch B b /\ T1 = T3 ++ b::nil.
Proof.
  unfold ImmAfter.
  intros A B a T1 T2 HmatchA Hib.
  rewrite rev_app_distr in Hib.
  simpl in Hib. rewrite <- app_assoc in Hib.
  eapply immbefore_ok in Hib; eauto.
  destruct Hib as [b H]. destruct H as [T3 H].
  exists b. exists (rev T3).
  destruct H.
  split.
    auto.

    rewrite <- rev_involutive with (l:=T1).
    rewrite H0. auto.
Qed.

Inductive Enables (past:KOAction) (future:KOAction)
  : KTrace -> Prop :=
| E_nil : Enables past future nil
| E_not_future : forall act tr, Enables past future tr ->
                                ~AMatch future act ->
                                Enables past future (act::tr)
| E_future : forall act tr, Enables past future tr ->
                            (exists past', In past' tr /\
                                           AMatch past past') ->
                            Enables past future (act::tr).

Lemma enables_ok :
  forall A B b T1 T2,
    AMatch B b ->
    Enables A B (T1 ++ b :: T2) ->
    exists a, exists T3, exists T4,
      AMatch A a /\ T2 = T3 ++ a :: T4.
Proof.
  intros A B b T1 T2 Hmatch Hen.
  remember (T1 ++ b :: T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction Hen; intros T2 T1 HT.
    pose (app_cons_not_nil T1 T2 b).
    contradiction.

    destruct T1.
      simpl in HT. inversion HT.
      subst b. contradiction.

      inversion HT. eauto.

    destruct T1.
      simpl in HT. inversion HT.
      subst tr.
      destruct H as [a H].
      destruct H as [Hin HmatchA].
      apply List.in_split in Hin.
      destruct Hin as [l1 rest].
      destruct rest as [l2 H].
      eauto.

      inversion HT. eauto.
Qed.

Definition Ensures A B tr := Enables B A (rev tr).

Lemma ensures_ok :
  forall A B a T1 T2,
    AMatch A a ->
    Ensures A B (T1 ++ a :: T2) ->
    exists b, exists T3, exists T4,
      AMatch B b /\ T1 = T3 ++ b :: T4.
Proof.
  unfold Ensures.
  intros A B a T1 T2 HmatchA Hen.
  rewrite rev_app_distr in Hen.
  simpl in Hen. rewrite <- app_assoc in Hen.
  eapply enables_ok in Hen; eauto.
  destruct Hen as [b H]. destruct H as [T3 H].
  destruct H as [T4 H].
  exists b. exists (rev T4).
  exists (rev T3).
  destruct H.
  split.
    auto.

    rewrite <- rev_involutive with (l:=T1).
    rewrite H0. rewrite List.rev_app_distr.
    simpl. rewrite <- List.app_assoc. auto.
Qed.

(*Definition Not_In (A:KOAction) (tr:KTrace) : Prop :=
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
Qed.        *)

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