Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexDenoted.
Require Import ActionMatch.
Require Import List.
Require Import Ynot.

Section PolLang.

Context {NB_MSG:nat}.
Variable PAYD:vvdesc NB_MSG.
Variable COMPT : Set.
Variable COMPS : COMPT -> compd.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Variable KSTD : vcdesc COMPT.
Definition KOAction := KOAction PAYD COMPT COMPS.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition kstate := kstate PAYD COMPT COMPS KSTD.
Definition AMatch := AMatch PAYD COMPT COMPS COMPTDEC.

(*Expressions over state variables. Currently, we only allow
  the user to write expressions about variables that are not
  comps.*)
Inductive KStateExpr : desc -> Type :=
| StVar : forall (i : fin (projT1 KSTD)) d,
            (svec_ith (projT2 KSTD) i) = Desc _ d ->
            KStateExpr d
| Const : forall d, s[[d]] -> KStateExpr d.

Inductive KStateRelation : Type :=
| Eq : forall d, KStateExpr d -> KStateExpr d -> KStateRelation
| Neq : forall d, KStateExpr d -> KStateExpr d -> KStateRelation
(*Should we allow > to be defined for any desc, or only num?*)
| Gt : KStateExpr num_d -> KStateExpr num_d -> KStateRelation
| Gte : KStateExpr num_d -> KStateExpr num_d -> KStateRelation.

Inductive Policy' : Type :=
| ImmAfter : KOAction -> KOAction -> Policy'
| ImmBefore : KOAction -> KOAction -> Policy'
| Contains : KOAction -> Policy'
| Enables : KOAction -> KOAction -> Policy'
| Disables : KOAction -> KOAction -> Policy'
| KstRel : KStateRelation -> Policy'
| Conj : Policy' -> Policy' -> Policy'.

Inductive Policy : Type :=
| Base : Policy' -> Policy
| Imp : Policy' -> Policy' -> Policy.

Inductive ImmAfterMatch (after:KOAction) (before:KOAction)
  : KTrace -> Prop :=
| IA_nil : ImmAfterMatch after before nil
(*An action not matching before is added*)
| IA_nB : forall before' tr, ImmAfterMatch after before tr ->
                             ~AMatch before before' ->
                             ImmAfterMatch after before (before'::tr)
(*An action matching before is added*)
| IA_B : forall before' after' tr, ImmAfterMatch after before tr ->
                                   AMatch after after' ->
                                   ImmAfterMatch after before (after'::before'::tr).

(*before occurs immediate before after occurs*)
Inductive ImmBeforeMatch (before:KOAction) (after:KOAction)
  : KTrace -> Prop :=
| IB_nil : ImmBeforeMatch before after nil
(*An action not matching after is added*)
| IB_nA : forall after' tr, ImmBeforeMatch before after tr ->
                            ~AMatch after after' ->
                            ImmBeforeMatch before after (after'::tr)
(*An action matching after is added*)
| IB_A : forall after' before' tr, ImmBeforeMatch before after tr ->
                                   AMatch before before' ->
                                   ImmBeforeMatch before after (after'::before'::tr).

Inductive ContainsMatch (A:KOAction) : KTrace -> Prop :=
| C_match : forall a tr, AMatch A a -> ContainsMatch A (a::tr)
| C_notMatch : forall x tr, ContainsMatch A tr -> ContainsMatch A (x::tr).

Inductive EnablesMatch (past:KOAction) (future:KOAction)
  : KTrace -> Prop :=
| E_nil : EnablesMatch past future nil
| E_not_future : forall act tr, EnablesMatch past future tr ->
                                ~AMatch future act ->
                                EnablesMatch past future (act::tr)
| E_future : forall act tr, EnablesMatch past future tr ->
                            ContainsMatch past tr ->
                            EnablesMatch past future (act::tr).

Inductive DisablesMatch (disabler:KOAction) (disablee:KOAction)
  : KTrace -> Prop :=
| D_nil : DisablesMatch disabler disablee nil
| D_not_disablee : forall act tr, DisablesMatch disabler disablee tr ->
                                  ~AMatch disablee act ->
                                  DisablesMatch disabler disablee (act::tr)
| D_disablee : forall act tr, DisablesMatch disabler disablee tr ->
                              ~ContainsMatch disabler tr ->
                              DisablesMatch disabler disablee (act::tr).

Fixpoint eval_kstate_expr d (expr : KStateExpr d) (st : kstate) : s[[d]] :=
  match expr with
  | StVar i _ Heq => match Heq in _ = _d return s[[svec_ith (projT2 KSTD) i]] -> s[[_d]]
                     with
                     | eq_refl => fun x => x
                     end (shvec_ith _ (projT2 KSTD) (kst _ _ _ _ st) i)
  | Const _ v     => v
  end.

Inductive KstRelMatch (st : kstate) : KStateRelation -> Prop :=
| KSM_Eq : forall d e1 e2, eval_kstate_expr d e1 st = eval_kstate_expr d e2 st ->
                           KstRelMatch st (Eq d e1 e2)
| KSM_Neq : forall d e1 e2, eval_kstate_expr d e1 st <> eval_kstate_expr d e2 st ->
                           KstRelMatch st (Neq d e1 e2)
| KSM_Gt : forall e1 e2, nat_of_num (eval_kstate_expr num_d e1 st) >
                         nat_of_num (eval_kstate_expr num_d e2 st) ->
                         KstRelMatch st (Gt e1 e2)
| KSM_Gte : forall e1 e2, nat_of_num (eval_kstate_expr num_d e1 st) >=
                          nat_of_num (eval_kstate_expr num_d e2 st) ->
                          KstRelMatch st (Gte e1 e2).

Definition liftKTraceProp (st : kstate) (pol : KTrace -> Prop) : Prop :=
  forall tr, ktr _ _ _ _ st = [tr]%inhabited -> pol tr.

Inductive PolicyMatch' : Policy' -> kstate -> Prop :=
| PM_ImmAfter : forall A B st, liftKTraceProp st (ImmAfterMatch A B) ->
                               PolicyMatch' (ImmAfter A B) st
| PM_ImmBefore : forall A B st, liftKTraceProp st (ImmBeforeMatch A B) ->
                                PolicyMatch' (ImmBefore A B) st
| PM_Contains : forall A st, liftKTraceProp st (ContainsMatch A) ->
                             PolicyMatch' (Contains A) st
| PM_Enables : forall A B st, liftKTraceProp st (EnablesMatch A B) ->
                              PolicyMatch' (Enables A B) st
| PM_Disables : forall A B st, liftKTraceProp st (DisablesMatch A B) ->
                               PolicyMatch' (Disables A B) st
| PM_Kst : forall st rel, KstRelMatch st rel -> PolicyMatch' (KstRel rel) st
| PM_Conj : forall st p1 p2, PolicyMatch' p1 st -> PolicyMatch' p2 st -> PolicyMatch' (Conj p1 p2) st.

Inductive PolicyMatch : Policy -> kstate -> Prop :=
| PM_Base : forall st p, PolicyMatch' p st -> PolicyMatch (Base p) st
| PM_Imp : forall st p1 p2, (PolicyMatch' p1 st -> PolicyMatch' p2 st) ->
                            PolicyMatch (Imp p1 p2) st.

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
Qed.        
*)

End PolLang.
