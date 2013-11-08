Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import List.

Require Import Coq.Logic.Eqdep.

Section Prune.

Context {NB_MSG : nat}.
Variable PAYD     : vvdesc NB_MSG.
Variable COMPT    : Set.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Variable COMPS    : COMPT -> compd.
Variable IENVD    : vcdesc COMPT.
Variable KSTD     : vcdesc COMPT.
Variable INIT : init_prog PAYD COMPT COMPS KSTD IENVD.
Variable HANDLERS : handlers PAYD COMPT COMPS KSTD.
Definition comp := comp COMPT COMPS.
Definition Reach := Reflex.Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT.
Definition ValidExchange := ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition KAction := KAction PAYD COMPT COMPS.
Definition kstate := kstate PAYD COMPT COMPS KSTD.
Definition ktr := ktr PAYD COMPT COMPS KSTD.
Definition Nop := Reflex.Nop PAYD COMPT COMPS KSTD.

Require Import NIExists.
Require Import Ynot.

Ltac uninhabit :=
  match goal with
  | [ H : inhabits _ = inhabits ?tr |- _ ]
    => apply pack_injective in H; subst tr
  end.

Ltac remove_redundant_ktr :=
  unfold NIExists.ktr in *;
  match goal with
  | [ H : Reflex.ktr _ _ _ _ ?s = inhabits ?tr,
      H' : Reflex.ktr _ _ _ _ ?s = inhabits ?tr' |- _ ]
    => rewrite H' in H; apply pack_injective in H; subst tr
  end.

Lemma prune_nop_1 : forall clblr vlblr cslblr c m i s s',
  ValidExchange c m i s s' ->
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  high_out_eq _ _ _ _ s s' clblr /\ vars_eq _ _ _ _ s s' vlblr /\ cs_eq _ _ _ _ s s' cslblr.
Proof.
  intros clblr vlblr cslblr c m i s s' Hve Hnop.
  inversion Hve. clear Hve.
    subst s'0. unfold hdlrs. generalize i. rewrite Hnop. 
    intros. simpl. unfold kstate_run_prog. unfold hdlr_state_run_cmd.
    simpl. split. 
      unfold high_out_eq. intros. simpl in *.
      uninhabit. simpl. remove_redundant_ktr. auto.

      split.
        unfold vars_eq. simpl. auto.

        unfold cs_eq. simpl. auto.
Qed.

Lemma prune_nop_2 : forall clblr vlblr cslblr c m i s1 s1' s2 s2',
  ValidExchange c m i s1 s1' ->
  ValidExchange c m i s2 s2' ->
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  high_out_eq _ _ _ _ s1 s2 clblr -> vars_eq _ _ _ _ s1 s2 vlblr ->
  cs_eq _ _ _ _ s1 s2 cslblr ->
  high_out_eq _ _ _ _ s1' s2' clblr /\ vars_eq _ _ _ _ s1' s2' vlblr /\
  cs_eq _ _ _ _ s1' s2' cslblr.
Proof.
  intros clblr vlblr cslblr c m i s1 s2 s1' s2' Hve1 Hve2 Hnop Hout Hvars.
  inversion Hve1. inversion Hve2. clear Hve1. clear Hve2.
    subst s'0. subst s'. unfold hdlrs. unfold hdlrs0. generalize i. rewrite Hnop. 
    intros. unfold kstate_run_prog. unfold hdlr_state_run_cmd.
    simpl. split. 
      unfold high_out_eq. intros. simpl in *.
      repeat uninhabit. simpl. auto.

      split.
        unfold vars_eq. simpl. auto.

        unfold cs_eq. simpl. auto.
Qed.

(*
Print high_ok.
Print kstate_run_prog.
Print high_out_eq.
Print mk_inter_ve_st.
Lemma skip_ve : forall clblr vlblr c m i s1 s1' s2 s2',
  high_out_eq PAYD COMPT COMPS KSTD s1 s2 clblr ->
  vars_eq PAYD COMPT COMPS KSTD s1 s2 vlblr ->
  Reflex.ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s1 s1' ->
  Reflex.ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s2 s2' ->
  (forall tr1 tr1' tr2 tr2',
    ktr _ _ _ _ s1 = inhabits tr1 ->
    ktr _ _ _ _ s1' = inhabits tr1' ->
    ktr _ _ _ _ s2 = inhabits tr2 ->
    ktr _ _ _ _ s2' = inhabits tr2' ->
    vars_eq PAYD COMPT COMPS KSTD s1 s2 vlblr ->
    high_out_eq PAYD COMPT COMPS KSTD
      (hdlr_kst _ _ _ _ _ (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m
        (projT1 (HANDLERS (tag _ m) (comp_type _ _ c)))
        (default_hdlr_state PAYD COMPT COMPS KSTD (mk_inter_ve_st _ _ _ _ c m s1 tr1)
          (projT1 (HANDLERS (tag _ m) (comp_type _ _ c))))
        (projT2 (HANDLERS (tag _ m) (comp_type _ _ c))) i))
      (hdlr_kst _ _ _ _ _ (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m
        (projT1 (HANDLERS (tag _ m) (comp_type _ _ c)))
        (default_hdlr_state PAYD COMPT COMPS KSTD (mk_inter_ve_st _ _ _ _ c m s2 tr1)
          (projT1 (HANDLERS (tag _ m) (comp_type _ _ c))))
        (projT2 (HANDLERS (tag _ m) (comp_type _ _ c))) i)) clblr)->
  high_out_eq PAYD COMPT COMPS KSTD s1' s2' clblr.
Proof.
  intros clblr vlblr c m i s1 s1' s2 s2' Hout Hvars Hve1 Hve2 Hunfolded.
  inversion Hve1. inversion Hve2. clear Hve1. clear Hve2.
    subst s'0. subst s'. unfold hdlrs. unfold hdlrs0.
    unfold kstate_run_prog. unfold hdlr_state_run_cmd.
        
*)

End Prune.