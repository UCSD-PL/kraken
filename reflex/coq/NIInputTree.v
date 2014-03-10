Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import List.
Require Import Ynot.
Require Import Coq.Logic.Eqdep.

Section NI.

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
Definition Reach := Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition KAction := KAction PAYD COMPT COMPS.
Definition kstate := kstate PAYD COMPT COMPS KSTD.
Definition ktr := ktr PAYD COMPT COMPS KSTD.
Definition kcs := kcs PAYD COMPT COMPS KSTD.

Definition init_input :=
  sdenote_itt (run_cmd_it PAYD COMPT COMPS KSTD INIT).

Record hdlr_input :=
  { cc : comp;
    cmsg : msg PAYD;
    input : sdenote_itt
      (run_cmd_it PAYD COMPT COMPS KSTD
        (projT2 ((HANDLERS (tag _ cmsg) (comp_type _ _ cc)))))
  }.

Record bogus_input :=
  { cbogus : comp;
    mbogus : @bogus_msg NB_MSG
  }.

Definition mk_inter_ve_st' c m s (tr:[KTrace]) :=
  let cs := kcs s in
  let tr := tr ~~~ KRecv _ _ _ c m :: KSelect _ _ _ cs c :: tr in
  {| Reflex.kcs := cs
   ; Reflex.ktr := tr
   ; Reflex.kst := kst _ _ _ _ s
   |}.

Definition mk_bogus_st' c bmsg s (tr:[KTrace]) :=
  let cs := kcs s in
  let tr := tr ~~~ KBogus _ _ _ c bmsg :: KSelect _ _ _ cs c :: tr in
  {| Reflex.kcs := cs
   ; Reflex.ktr := tr
   ; Reflex.kst := kst _ _ _ _ s
   |}.

Definition desc_eq_dec {d:desc} :
  forall (e1 e2:s[[d]]), decide (e1 = e2) :=
  match d as _d return
    forall (e1 e2:s[[_d]]), decide (e1 = e2)
  with
  | num_d => num_eq
  | str_d => str_eq
  | fd_d  => fd_eq
  end.

Fixpoint shvec_eq_dec (n:nat):
  forall (vd:svec desc n) (v1 v2:shvec sdenote_desc vd),
    decide (v1 = v2).
refine (
  match n as _n return
    forall (vd:svec desc _n) (v1 v2:shvec sdenote_desc vd),
      decide (v1 = v2)
  with
  | O => fun _ _ _ => left _ _
  | S n' => fun (vd:svec desc (S n')) =>
    match vd as _vd return
      forall (v1 v2: @shvec desc sdenote_desc (S n') _vd), decide (v1 = v2)
    with
    | (h, vd') => fun v1 v2 =>
      match desc_eq_dec (fst v1) (fst v2) with
      | left _ => 
        match shvec_eq_dec n' vd' (snd v1) (snd v2) with
        | left _ => left _ _
        | right _ => right _ _
        end
      | right _ => right _ _
      end
    end
  end);
destruct v1; destruct v2;
  solve [reflexivity |
    simpl in *; congruence].
Qed.

Definition comp_eq_dec (c1 c2:comp) : decide (c1 = c2).
refine (
  match c1, c2 with
  | Build_comp ct1 f1 cfg1, Build_comp ct2 f2 cfg2 =>
    match COMPTDEC ct1 ct2 with
    | left _ =>
      match fd_eq f1 f2 with
      | left _ => _
      | right _ => right _ _
      end
    | right _ => right _ _
    end
  end).
subst ct1. destruct (shvec_eq_dec _ _ cfg1 cfg2).
  left. congruence.
  right. intuition. inversion H.
  apply inj_pair2 in H2. auto.
intuition. inversion H. auto.
congruence.
Qed.

Fixpoint ReachFix (i_init:init_input)
  (i_hdlrs:list (hdlr_input + bogus_input)) : option kstate :=
  match i_hdlrs with
  | nil =>
    let s := init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD IENVD
      (initial_init_state PAYD COMPT COMPS KSTD IENVD) INIT i_init in
     Some {| Reflex.kcs := init_comps _ _ _ _ _ s
           ; Reflex.ktr := init_ktr _ _ _ _ _ s
           ; Reflex.kst := init_kst _ _ _ _ _ s
           |}
  | i_hdlr :: i_hdlrs' =>
    match ReachFix i_init i_hdlrs' with
    | Some s =>
      let (cs, tr, st) := s in
      match i_hdlr with
      | inl i_hdlr =>
        let c := cc i_hdlr in
        if List.in_dec comp_eq_dec c cs
        then let m := cmsg i_hdlr in
             let s' := mk_inter_ve_st' c m s tr in
             let hdlrs := HANDLERS (tag _ m) (comp_type _ _ c) in
               Some (kstate_run_prog _ _ COMPTDEC _ _ c m (projT1 hdlrs) s'
                 (projT2 hdlrs) (input i_hdlr))
        else None
      | inr i_hdlr =>
        let c := cbogus i_hdlr in
        if List.in_dec comp_eq_dec c cs
        then Some (mk_bogus_st' (cbogus i_hdlr) (mbogus i_hdlr) s tr)
        else None
      end
    | None => None
    end
  end.

Lemma Reach_ReachFix : forall s, Reach s ->
  exists i_init, exists i_hdlrs,
    ReachFix i_init i_hdlrs = Some s.
Proof.
  intros s HReach. induction HReach.
    destruct H. exists input0. exists nil.
    subst s. auto.

    destruct H. destruct IHHReach as [i_init [i_hdlrs IHHReach] ].
    exists i_init. exists (inl _ (Build_hdlr_input c m input0) :: i_hdlrs).
    simpl. subst s'. rewrite IHHReach. destruct s as [? [?] ?].
    simpl in *. apply pack_injective in H0. subst k. unfold hdlrs.
    destruct (in_dec comp_eq_dec c kcs0). auto. contradiction.

    destruct H. destruct IHHReach as [i_init [i_hdlrs IHHReach] ].
    exists i_init. exists (inr _ (Build_bogus_input c bmsg) :: i_hdlrs).
    simpl. rewrite IHHReach. destruct s as [? [?] ?].
    simpl in *. apply pack_injective in H0. subst k.
    destruct (in_dec comp_eq_dec c kcs0). auto. contradiction.
Qed.

Lemma ReachFix_Reach : forall i_init i_hdlrs s,
  ReachFix i_init i_hdlrs = Some s ->
  Reach s.
Proof.
  intros i_init i_hdlrs.
  induction i_hdlrs as [ | i_hdlr i_hdlrs];
    intros s HReachFix.
    simpl in *. inversion HReachFix.
    eapply Reach_init; eauto.
    constructor; auto.

    destruct i_hdlr. simpl in *.
    destruct (ReachFix i_init i_hdlrs).
    destruct k as [? [?] ?]. destruct (in_dec comp_eq_dec (cc h) kcs0).
    inversion HReachFix. eapply Reach_valid; eauto.
    apply IHi_hdlrs; eauto.
    econstructor; eauto.

    discriminate.
    discriminate.

    simpl in *. destruct (ReachFix i_init i_hdlrs).
    destruct k as [? [?] ?]. destruct (in_dec comp_eq_dec (cbogus b) kcs0).
    inversion HReachFix. eapply Reach_bogus; eauto.
    apply IHi_hdlrs; eauto.
    unfold mk_bogus_st'. simpl. econstructor; eauto.

    discriminate.
    discriminate.
Qed.

Definition is_high (clblr:comp->bool) (i:hdlr_input + bogus_input) :=
  match i with
  | inl i => clblr (cc i)
  | inr i => clblr (cbogus i)
  end.

Definition high (clblr:comp->bool) (i:list (hdlr_input + bogus_input)) :=
  filter (is_high clblr) i.

Definition is_output labeler (act : KAction) :=
  match act with
  | KSend c _   => labeler c
  | KExec _ _ c => labeler c
  | _           => false
  end.

Definition outputs labeler (tr : KTrace) :=
  filter (is_output labeler) tr.

Definition high_out_eq (s s' : kstate) clblr :=
  forall tr tr',
    ktr s = [tr]%inhabited ->
    ktr s' = [tr']%inhabited ->
    outputs clblr tr = outputs clblr tr'.

Definition vars_eq (s1 s2 : kstate)
  (lblr : fin (projT1 KSTD) -> bool) :=  
  shvec_erase _ lblr _ (kst _ _ _ _ s1) = shvec_erase _ lblr _ (kst _ _ _ _ s2).

Definition cs_eq (s1 s2 : kstate) cslblr :=
  filter cslblr (kcs s1) = filter cslblr (kcs s2).

Definition NI clblr vlblr cslblr :=
  forall i_init i1 i2 s1 s2,
    high clblr i1 = high clblr i2 ->
    ReachFix i_init i1 = Some s1 ->
    ReachFix i_init i2 = Some s2 ->
    high_out_eq s1 s2 clblr /\
    vars_eq s1 s2 vlblr /\
    cs_eq s1 s2 cslblr.

Definition low_ok clblr vlblr cslblr := forall c m i s s',
  clblr c = false ->
  Reach s ->
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s s' ->
  high_out_eq s s' clblr /\
  vars_eq s s' vlblr /\
  cs_eq s s' cslblr.

Definition high_ok clblr vlblr cslblr :=
  forall c m i s1 s1' s2 s2',
    clblr c = true ->
    high_out_eq s1 s2 clblr ->
    vars_eq s1 s2 vlblr ->
    cs_eq s1 s2 cslblr ->
    Reach s1 -> Reach s2 ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s1 s1' ->
    ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS c m i s2 s2' ->
    high_out_eq s1' s2' clblr /\ vars_eq s1' s2' vlblr /\
    cs_eq s1' s2' cslblr.

Ltac uninhabit :=
  match goal with
  | [ H : [_]%inhabited = [?tr]%inhabited |- _ ]
    => apply pack_injective in H; subst tr
  end.

Definition high_comp_pat COMPT COMPTDEC COMPS cp clblr :=
  forall c, match_comp COMPT COMPTDEC COMPS cp c = true ->
    clblr c = true.

Definition exec_comps (a : KAction) (l : list comp) : list comp :=
  match a with
  | Reflex.KExec _ _ c => c::l
  | _           => l
  end.

Lemma high_out_eq_sym : forall s s' clblr,
  high_out_eq s s' clblr -> high_out_eq s' s clblr.
Proof.
  unfold high_out_eq. intros.
  symmetry. auto.
Qed.

Lemma vars_eq_sym : forall s s' clblr,
  vars_eq s s' clblr -> vars_eq s' s clblr.
Proof.
  unfold vars_eq. intros.
  symmetry. auto.
Qed.

Lemma cs_eq_sym : forall s s' clblr,
  cs_eq s s' clblr -> cs_eq s' s clblr.
Proof.
  unfold cs_eq. intros.
  symmetry. auto.
Qed.

Lemma hout_init' : forall clblr envd s cmd input tr tr',
  init_ktr _ _ _ _ _ s = [tr]%inhabited ->
  filter clblr (init_comps _ _ _ _ _ s) = fold_right exec_comps nil (outputs clblr tr) ->
  let s' := init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd s cmd input in
  init_ktr _ _ _ _ _ s' = [tr']%inhabited ->
  filter clblr (init_comps _ _ _ _ _ s') = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr envd s cmd input tr tr' Htr Heq s' Htr'. subst s'.
  generalize dependent s. generalize dependent tr. generalize dependent tr'.
  induction cmd; simpl; intros tr' tr s Htr Heq Htr'.
    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (init_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD envd s cmd1
              (fst input)) as [? [itr] ? ?]_eqn.
    apply IHcmd2 with (tr:=itr); auto.
    rewrite <- Heqi.
    apply IHcmd1 with (tr:=tr); auto.
    rewrite Heqi. auto.

    destruct (num_eq
              (eval_base_expr COMPT COMPS
                 (init_env PAYD COMPT COMPS KSTD envd s) e) FALSE).
      apply IHcmd2 with (tr:=tr); auto.
      apply IHcmd1 with (tr:=tr); auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl.
    destruct (clblr
           (projT1
              (eval_base_expr COMPT COMPS
                 (init_env PAYD COMPT COMPS KSTD envd s) e))); auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl.
    destruct (clblr
         {|
         comp_type := t;
         comp_fd := input;
         comp_conf := eval_base_payload_expr COMPT COMPS envd
                        (init_env PAYD COMPT COMPS KSTD envd s)
                        (comp_conf_desc COMPT COMPS t) p |}); auto.
    simpl. f_equal. auto.

    rewrite Htr in *. simpl in *. apply pack_injective in Htr'.
    subst tr'. simpl. auto.

    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (find_comp COMPT COMPTDEC COMPS
               (eval_base_comp_pat COMPT COMPS envd
                  (init_env PAYD COMPT COMPS KSTD envd s) cp)
               (init_comps PAYD COMPT COMPS KSTD envd s)).
      apply IHcmd1 with (tr:=tr); auto.
      apply IHcmd2 with (tr:=tr); auto.
Qed.

Lemma hout_init : forall clblr init i s tr,
  InitialState PAYD COMPT COMPTDEC COMPS KSTD IENVD init i s ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr).
Proof.
  intros clblr init i s tr Hinit Htr.
  inversion Hinit. subst s0.
  destruct (initial_init_state PAYD COMPT COMPS KSTD IENVD) as [ics [itr] ? ?]_eqn.
  assert (filter clblr ics = fold_right exec_comps nil (outputs clblr itr)).
    unfold initial_init_state in *. inversion Heqi0.
    apply f_equal with (f:=init_ktr _ _ _ _ _ ) in Heqi0.
    simpl in Heqi0. apply pack_injective in Heqi0. subst itr. auto.
  simpl. apply hout_init' with (tr:=itr); auto.
  subst s. auto.
Qed.

Lemma hout_hdlr' : forall clblr envd cc m s cmd input tr tr',
  ktr (hdlr_kst _ _ _ _ envd s) = [tr]%inhabited ->
  filter clblr (kcs (hdlr_kst _ _ _ _ _ s)) = fold_right exec_comps nil (outputs clblr tr) ->
  let s' := hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD cc m envd s cmd input in
  ktr (hdlr_kst _ _ _ _ _ s') = [tr']%inhabited ->
  filter clblr (kcs (hdlr_kst _ _ _ _ _ s')) = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr envd cc m s cmd input tr tr' Htr Heq s' Htr'. subst s'.
  generalize dependent s. generalize dependent tr. generalize dependent tr'.
  induction cmd; simpl; intros tr' tr s Htr Heq Htr'.
    rewrite Htr in Htr'. apply pack_injective in Htr'. subst tr'. auto.

    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD cc m envd s
                 cmd1 (fst input)) as [ [? [itr] ?] ?]_eqn.
    apply IHcmd2 with (tr:=itr); auto.
    rewrite <- Heqh.
    apply IHcmd1 with (tr:=tr); auto.
    rewrite Heqh. auto.

    destruct (num_eq
                 (eval_hdlr_expr PAYD COMPT COMPS KSTD cc m
                    (kst PAYD COMPT COMPS KSTD
                       (hdlr_kst PAYD COMPT COMPS KSTD envd s))
                    (hdlr_env PAYD COMPT COMPS KSTD envd s) e) FALSE).
      apply IHcmd2 with (tr:=tr); auto.
      apply IHcmd1 with (tr:=tr); auto.

    
    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl.
    destruct (clblr
           (projT1
              (eval_hdlr_expr PAYD COMPT COMPS KSTD cc m
                 (kst PAYD COMPT COMPS KSTD hdlr_kst) hdlr_env e))); auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl.
    destruct (clblr
           {|
           comp_type := t;
           comp_fd := input;
           comp_conf := eval_hdlr_payload_expr PAYD COMPT COMPS KSTD cc m
                          (kst PAYD COMPT COMPS KSTD hdlr_kst) envd hdlr_env
                          (comp_conf_desc COMPT COMPS t) p |}); auto.
    simpl. f_equal. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in *. simpl in *.
    apply pack_injective in Htr'. subst tr'. simpl. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in Htr'.
    apply pack_injective in Htr'. subst tr'. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in Htr'.
    apply pack_injective in Htr'. subst tr'. auto.

    destruct s. simpl in *. unfold ktr in *. rewrite Htr in Htr'.
    apply pack_injective in Htr'. subst tr'. auto.

    destruct s. simpl in *.
    destruct (find_comp COMPT COMPTDEC COMPS
                  (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD cc m
                     (kst PAYD COMPT COMPS KSTD hdlr_kst) envd hdlr_env cp)
                  (Reflex.kcs _ _ _ _ hdlr_kst)).
      apply IHcmd1 with (tr:=tr); auto.
      apply IHcmd2 with (tr:=tr); auto.
Qed.

Lemma hout_hdlr : forall clblr cc m s s' input tr tr',
  ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS cc m input s s' ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr) ->
  ktr s' = [tr']%inhabited ->
  filter clblr (kcs s') = fold_right exec_comps nil (outputs clblr tr').
Proof.
  intros clblr cc m s s' input tr tr' Hve Htr Heq Htr'.
  inversion Hve. subst s'0. unfold kstate_run_prog.
  destruct ((default_hdlr_state PAYD COMPT COMPS KSTD
                 (mk_inter_ve_st PAYD COMPT COMPS KSTD cc m s tr0)
                 (projT1 hdlrs))) as [ [ ? [itr] ? ] ? ]_eqn.
    apply hout_hdlr' with (tr:=itr); auto.
    rewrite <- Heqh. unfold default_hdlr_state, mk_inter_ve_st in Heqh.
    apply f_equal with (f:=fun s => ktr (hdlr_kst _ _ _ _ _ s)) in Heqh.
    simpl in *. apply pack_injective in Heqh. subst itr. simpl.
    unfold ktr in Htr. rewrite H0 in Htr. apply pack_injective in Htr.
    subst tr0. auto.
    unfold kstate_run_prog in *. rewrite Heqh in *.
    rewrite H3. auto.
Qed.

Lemma hout_hcs : forall clblr s tr,
  Reach s ->
  ktr s = [tr]%inhabited ->
  filter clblr (kcs s) = fold_right exec_comps nil (outputs clblr tr).
Proof.
  intros clblr s tr HReach Htr.
  generalize dependent tr.
  induction HReach; intros tr Htr.
    eapply hout_init; eauto.

    destruct s as [? [itr] ?]_eqn.
    eapply hout_hdlr; eauto.

    inversion H. subst s'. simpl in *.
    apply pack_injective in Htr. subst tr.
    simpl. eapply IHHReach; eauto.
Qed.

Lemma hout_eq_hcs_eq : forall s s' clblr,
  Reach s -> Reach s' ->
  high_out_eq s s' clblr ->
  filter clblr (kcs s) = filter clblr (kcs s').
Proof.
  intros s s' clblr HReach HReach' Hout_eq.
  destruct s as [ ? [tr] ? ]; destruct s' as [ ? [tr'] ? ].
  rewrite hout_hcs with (tr:=tr); auto.
  rewrite hout_hcs with (tr:=tr'); auto.
  rewrite Hout_eq; auto.
Qed.

Lemma hfind_cs_filter : forall cs clblr cp,
  high_comp_pat COMPT COMPTDEC COMPS cp clblr ->
  find_comp COMPT COMPTDEC COMPS cp cs = 
  find_comp COMPT COMPTDEC COMPS cp (filter clblr cs).
Proof.
  intros cs clblr cp Hhigh.
  induction cs.
    auto.

    simpl. destruct (clblr a) as [ | ]_eqn. simpl.
    destruct (match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [ ? | ? ]_eqn; auto.
    destruct (match_comp_pf COMPT COMPTDEC COMPS cp a)
      as [ ? | ? ]_eqn.
    unfold high_comp_pat, match_comp in Hhigh. specialize (Hhigh a).
    rewrite Heqo in Hhigh. specialize (Hhigh (Logic.eq_refl _)). congruence.
    auto.
Qed.

Lemma hout_eq_find_eq1 : forall cp s s' clblr,
  Reach s -> Reach s' ->
  high_out_eq s s' clblr ->
  high_comp_pat COMPT COMPTDEC COMPS cp clblr ->
  find_comp COMPT COMPTDEC COMPS cp (Reflex.kcs _ _ _ _ s) = 
  find_comp COMPT COMPTDEC COMPS cp (Reflex.kcs _ _ _ _ s').
Proof.
  intros cp s s' clblr HReach HReach' Hout_eq Hcp.
  rewrite hfind_cs_filter with (clblr:=clblr) (cs:=Reflex.kcs _ _ _ _ s); auto.
  rewrite hfind_cs_filter with (clblr:=clblr) (cs:=Reflex.kcs _ _ _ _ s'); auto.
  erewrite hout_eq_hcs_eq; auto.
Qed.

Lemma hout_eq_find_eq2 : forall cp s s' cslblr,
  cs_eq s s' cslblr ->
  high_comp_pat COMPT COMPTDEC COMPS cp cslblr ->
  find_comp COMPT COMPTDEC COMPS cp (Reflex.kcs _ _ _ _ s) = 
  find_comp COMPT COMPTDEC COMPS cp (Reflex.kcs _ _ _ _ s').
Proof.
  intros cp s s' cslblr Hcs_eq Hcp.
  rewrite hfind_cs_filter with (clblr:=cslblr) (cs:=Reflex.kcs _ _ _ _ s); auto.
  rewrite hfind_cs_filter with (clblr:=cslblr) (cs:=Reflex.kcs _ _ _ _ s'); auto.
  rewrite Hcs_eq. auto.
Qed.

Lemma high_out_eq_trans : forall s1 s2 s3 clblr,
  high_out_eq s1 s2 clblr ->
  high_out_eq s2 s3 clblr ->
  high_out_eq s1 s3 clblr.
Proof.
  intros s1 s2 s3 clblr H1 H2.
  unfold high_out_eq in *.
  intros t1 tr3 Htr1 Htr3.
  destruct s2 as [? [tr2] ?].
  transitivity (outputs clblr tr2); auto.
Qed.

Lemma vars_eq_trans : forall s1 s2 s3 vlblr,
  vars_eq s1 s2 vlblr ->
  vars_eq s2 s3 vlblr ->
  vars_eq s1 s3 vlblr.
Proof.
  intros s1 s2 s3 vlblr H1 H2.
  unfold vars_eq in *. congruence.
Qed.

Lemma cs_eq_trans : forall s1 s2 s3 cslblr,
  cs_eq s1 s2 cslblr ->
  cs_eq s2 s3 cslblr ->
  cs_eq s1 s3 cslblr.
Proof.
  intros s1 s2 s3 cslblr H1 H2.
  unfold cs_eq in *. congruence.
Qed.

Lemma ni_nil_hdlr : forall clblr vlblr cslblr s1 s2 i_init i_hdlrs i_hdlr,
  ReachFix i_init nil = Some s1 ->
  ReachFix i_init (i_hdlr :: i_hdlrs) = Some s2 ->
  low_ok clblr vlblr cslblr ->
  high clblr nil = high clblr (i_hdlr :: i_hdlrs) ->
  (forall s1 s2, high clblr nil = high clblr i_hdlrs ->
    ReachFix i_init nil = Some s1 ->
    ReachFix i_init i_hdlrs = Some s2 ->
     high_out_eq s1 s2 clblr /\ vars_eq s1 s2 vlblr /\ cs_eq s1 s2 cslblr) ->
  high_out_eq s1 s2 clblr /\ vars_eq s1 s2 vlblr /\ cs_eq s1 s2 cslblr.
Proof.
  intros clblr vlblr cslblr s1 s2 i_init i_hdlrs i_hdlr HFix1 HFix2 Hlow Hin IHi2.
  destruct i_hdlr. simpl in Hin.
      destruct (clblr (cc h)) as [? | ?]_eqn. discriminate.
      unfold low_ok in Hlow. simpl in *.
      destruct (ReachFix i_init i_hdlrs) as [ s2' | ]_eqn;
        try discriminate. inversion HFix1.
      repeat split;
        first [eapply high_out_eq_trans with (s2:=s2') |
               eapply vars_eq_trans with (s2:=s2') |
               eapply cs_eq_trans with (s2:=s2')]; eauto.
        apply IHi2; auto. eapply Hlow; eauto.
        eapply ReachFix_Reach; eauto.
        destruct s2' as [? [?] ?].
        destruct (in_dec comp_eq_dec (cc h) kcs0); try discriminate.
        inversion HFix2. econstructor; eauto.

        apply IHi2; auto. eapply Hlow; eauto.
        eapply ReachFix_Reach; eauto.
        destruct s2' as [? [?] ?].
        destruct (in_dec comp_eq_dec (cc h) kcs0); try discriminate.
        inversion HFix2. econstructor; eauto.

        apply IHi2; auto. eapply Hlow; eauto.
        eapply ReachFix_Reach; eauto.
        destruct s2' as [? [?] ?].
        destruct (in_dec comp_eq_dec (cc h) kcs0); try discriminate.
        inversion HFix2. econstructor; eauto.

        simpl in *. destruct (clblr (cbogus b)) as [? | ?]_eqn.
        discriminate.
        destruct (ReachFix i_init i_hdlrs) as [ s2' | ];
        try discriminate. inversion HFix1.
        destruct s2' as [? [?] ?].
        destruct (in_dec comp_eq_dec (cbogus b) kcs0); try discriminate.
        inversion HFix2. unfold mk_bogus_st'. simpl.
        repeat split.
          unfold high_out_eq. intros. simpl in *. uninhabit.
          simpl. eapply IHi2; eauto. subst s1. simpl. auto.

          unfold vars_eq in *. simpl in *.
          match type of IHi2 with
          | forall s1 s2, _ -> Some ?s1' = Some s1 -> Some ?s2' = Some s2 -> _ =>
            specialize (IHi2 s1' s2')
          end. simpl in *. apply IHi2; auto.

          unfold cs_eq in *. simpl in *.
          match type of IHi2 with
          | forall s1 s2, _ -> Some ?s1' = Some s1 -> Some ?s2' = Some s2 -> _ =>
            specialize (IHi2 s1' s2')
          end. simpl in *. apply IHi2; auto.
Qed.

Lemma obl_sym : forall clblr vlblr cslblr s1 s2,
  high_out_eq s1 s2 clblr /\ vars_eq s1 s2 vlblr /\ cs_eq s1 s2 cslblr ->
  high_out_eq s2 s1 clblr /\ vars_eq s2 s1 vlblr /\ cs_eq s2 s1 cslblr.
Proof.
  intros.
repeat split;
  first [apply high_out_eq_sym |
         apply vars_eq_sym |
         apply cs_eq_sym]; apply H.
Qed.

Lemma obl_trans : forall clblr vlblr cslblr s1 s2 s3,
  high_out_eq s1 s2 clblr /\ vars_eq s1 s2 vlblr /\ cs_eq s1 s2 cslblr ->
  high_out_eq s2 s3 clblr /\ vars_eq s2 s3 vlblr /\ cs_eq s2 s3 cslblr ->
  high_out_eq s1 s3 clblr /\ vars_eq s1 s3 vlblr /\ cs_eq s1 s3 cslblr.
Proof.
  intros.
  repeat split;
    first [apply (high_out_eq_trans s1 s2 s3) |
           apply (vars_eq_trans s1 s2 s3) |
           apply (cs_eq_trans s1 s2 s3) ]; tauto.
Qed.

Theorem ni_suf : forall clblr vlblr cslblr,
  low_ok clblr vlblr cslblr ->
  high_ok clblr vlblr cslblr ->
  NI clblr vlblr cslblr.
Proof.
  unfold NI.
  intros clblr vlblr cslblr Hlow Hhigh i_init i1.
  induction i1 as [ | i_hdlr1 i1]; intros i2.
    induction i2 as [ | i_hdlr2 i2]; intros s1 s2 Hin HFix1 HFix2.
      simpl in *. inversion HFix1. inversion HFix2.
      subst s1. subst s2. repeat split.
      unfold high_out_eq. intros tr1 tr2 Htr1 Htr2.
      rewrite Htr1 in Htr2. uninhabit. auto.

      eapply ni_nil_hdlr; eauto.

      intros s1 s2 Hin HFix1 HFix2.
      destruct i_hdlr1 as [i_hdlr1 | i_hdlr1]; simpl in *.
        destruct (clblr (cc i_hdlr1)) as [? | ?]_eqn.
        generalize dependent Hin.
        generalize dependent s2.
        generalize dependent s1.
        induction i2 as [ | i_hdlr2 i2]; intros s1 HFix1 s2 HFix2 Hin.
          apply obl_sym.
          apply (ni_nil_hdlr clblr vlblr cslblr s2 s1 i_init i1 (inl _ i_hdlr1)); auto.
          simpl. rewrite Heqb. auto. intros. apply obl_sym.
          eapply (IHi1 nil); eauto.

          destruct i_hdlr2 as [i_hdlr2 | i_hdlr2]; simpl in *.
            destruct (clblr (cc i_hdlr2)) as [? | ?]_eqn.
              inversion Hin; subst i_hdlr1.
              destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                 destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                   try discriminate;
                     destruct s1' as [? [?] ?]_eqn;
                       destruct s2' as [? [?] ?]_eqn;
                         repeat match goal with
                          | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                           => destruct (List.in_dec dec c cs)
                          end; try discriminate.
              apply (Hhigh (cc i_hdlr2) (cmsg i_hdlr2) (input i_hdlr2) s1' s1 s2' s2); auto;
                subst s1'; subst s2';
                  try solve [eapply IHi1; eauto |
                    eapply ReachFix_Reach; eauto].
              inversion HFix1; subst s1; econstructor; eauto.
              inversion HFix2; subst s2; econstructor; eauto.

              destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                 destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                   try discriminate;
                     destruct s1' as [? [?] ?]_eqn;
                       destruct s2' as [? [?] ?]_eqn;
                         repeat match goal with
                          | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                           => destruct (List.in_dec dec c cs)
                          end; try discriminate.
              apply obl_trans with (s2:=s2').
              apply IHi2; auto. congruence.
              apply (Hlow (cc i_hdlr2) (cmsg i_hdlr2) (input i_hdlr2) s2' s2); auto.
              subst s2'. eapply ReachFix_Reach; eauto.
              subst s2'. inversion HFix2. subst s2. econstructor; eauto.

              destruct (clblr (cbogus i_hdlr2)); try discriminate.
              destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                 destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                   try discriminate;
                     destruct s1' as [? [?] ?]_eqn;
                       destruct s2' as [? [?] ?]_eqn;
                         repeat match goal with
                          | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                           => destruct (List.in_dec dec c cs)
                          end; try discriminate.
              subst s2'. specialize (IHi2 s1 HFix1 _ (Logic.eq_refl _) Hin).
              unfold mk_bogus_st' in HFix2. simpl in *. inversion HFix2.
              repeat split.
                unfold high_out_eq. intros. simpl in *. repeat uninhabit. simpl.
                apply IHi2; auto.
                unfold vars_eq. simpl. apply IHi2; auto.
                unfold cs_eq. simpl. apply IHi2; auto.
              
        destruct (ReachFix i_init i1) as [ s1' |]_eqn;
            try discriminate;
              destruct s1' as [? [?] ?]_eqn;
                repeat match goal with
                | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                  => destruct (List.in_dec dec c cs)
                end; try discriminate.
        apply obl_trans with (s2:=s1').
        apply obl_sym.
        apply (Hlow (cc i_hdlr1) (cmsg i_hdlr1) (input i_hdlr1) s1' s1); auto;
          subst s1'.
        eapply ReachFix_Reach; eauto.
        inversion HFix1; subst s1; econstructor; eauto.
              
        eapply IHi1; eauto; subst s1'; auto.

        destruct (clblr (cbogus i_hdlr1)) as [? | ?]_eqn.
          generalize dependent Hin.
          generalize dependent s2.
          generalize dependent s1.
          induction i2 as [ | i_hdlr2 i2]; intros s1 HFix1 s2 HFix2 Hin.
            apply obl_sym.
            apply (ni_nil_hdlr clblr vlblr cslblr s2 s1 i_init i1 (inr _ i_hdlr1)); auto.
            simpl. rewrite Heqb. auto. intros. apply obl_sym.
            eapply (IHi1 nil); eauto.

            destruct i_hdlr2 as [i_hdlr2 | i_hdlr2];
              try discriminate; simpl in *.
               destruct (clblr (cc i_hdlr2)) as [? | ?]_eqn;
                 try discriminate.
                 destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                   destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                     try discriminate;
                       destruct s1' as [? [?] ?]_eqn;
                         destruct s2' as [? [?] ?]_eqn;
                           repeat match goal with
                           | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                             => destruct (List.in_dec dec c cs)
                           end; try discriminate.
                 inversion HFix1. subst s1.
                 apply obl_trans with (s2:=s2').
                 eapply IHi2; eauto. congruence.
                 subst s2'. inversion HFix2. subst s2.
                 eapply Hlow; eauto.
                 eapply ReachFix_Reach; eauto.
                 econstructor; eauto.

              destruct (clblr (cbogus i_hdlr2)) as [? | ?]_eqn.
                destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                   destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                     try discriminate;
                       destruct s1' as [? [?] ?]_eqn;
                         destruct s2' as [? [?] ?]_eqn;
                           repeat match goal with
                           | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                             => destruct (List.in_dec dec c cs)
                           end; try discriminate.
                inversion HFix1; inversion HFix2; subst s1; subst s2.
                unfold mk_bogus_st'. simpl.
                inversion Hin.
                repeat split.
                  unfold high_out_eq; intros. simpl in *. repeat uninhabit.
                  simpl. eapply (IHi1 i2 s1' s2'); eauto. subst s1'. auto.
                  subst s2'. auto. subst s1'. auto. subst s2'. auto.
                  unfold vars_eq; simpl.
                  subst s1'. subst s2'.
                  apply (IHi1 i2 _ _ H1 (Logic.eq_refl _) Heqo0).
                  unfold cs_eq; simpl.
                  subst s1'. subst s2'.
                  apply (IHi1 i2 _ _ H1 (Logic.eq_refl _) Heqo0).

                destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                   destruct (ReachFix i_init i2) as [ s2' |]_eqn;
                     try discriminate;
                       destruct s1' as [? [?] ?]_eqn;
                         destruct s2' as [? [?] ?]_eqn;
                           repeat match goal with
                           | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                             => destruct (List.in_dec dec c cs)
                           end; try discriminate.
                inversion HFix1; inversion HFix2; subst s1; subst s2.
                specialize (IHi2 _ (Logic.eq_refl _) _ (Logic.eq_refl _) Hin).
                eapply obl_trans. apply IHi2.
                repeat split.
                  unfold high_out_eq; intros. simpl in *. repeat uninhabit.
                  simpl. reflexivity.

                destruct (ReachFix i_init i1) as [ s1' |]_eqn;
                     try discriminate;
                       destruct s1' as [? [?] ?]_eqn;
                           repeat match goal with
                           | [ _ : context [List.in_dec ?dec ?c ?cs] |- _ ]
                             => destruct (List.in_dec dec c cs)
                           end; try discriminate.
                inversion HFix1. subst s1.
                unfold mk_bogus_st'. simpl.
                repeat split.
                  unfold high_out_eq. intros. simpl in *. uninhabit.
                  simpl. eapply IHi1; eauto.
                  unfold vars_eq; simpl. apply (IHi1 i2 _ _ Hin (Logic.eq_refl _) HFix2); eauto.
                  unfold cs_eq; simpl. apply (IHi1 i2 _ _ Hin (Logic.eq_refl _) HFix2); eauto.
Qed.

End NI.