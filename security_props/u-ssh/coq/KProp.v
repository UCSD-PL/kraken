Require Import Ascii.
Require Import List.
Require Import String.
Require Import Ynot.
Require Import Message.
Require Import Kernel.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

(* REMEMBER : traces are in reverse chrono order
 * so most recent event is in head position and
 * first action is last
 *)

Ltac inv H :=
  inversion H; subst; clear H.

Ltac uninhabit_step :=
  match goal with
  | [ H: inhabit_unpack (ktr ?s) _ = [_]%inhabited |- _ ] =>
    destruct s; simpl in *
  | [ H: inhabit_unpack ?itr _ = [_]%inhabited |- _ ] =>
    unfold itr in *
  | [ H: inhabit_unpack ?itr _ = [_]%inhabited |- _ ] =>
    destruct itr; simpl in *
  | [ H: [_]%inhabited = [_]%inhabited |- _ ] =>
    apply pack_injective in H;
    rewrite -> H in * || rewrite <- H in *
  | [ IH: forall ktr, [?ktr']%inhabited = [ktr]%inhabited -> _ |- _ ] =>
    specialize (IH ktr' (refl_equal _))
  end.

Ltac uninhabit :=
  repeat uninhabit_step.

(* if you see aft in a trace,
 * then it is immediately chrono preceded by bef
 *)
Definition ImmBefore (bef aft : KTrace) : Prop :=
  forall kst, KInvariant kst ->
  forall x y, ktr kst = [x ++ aft ++ y]%inhabited ->
  exists z, y = bef ++ z.

(* if you see bef in a trace,
 * then it is immediately chrono followed by aft
 *)
Definition ImmAfter (bef aft : KTrace) : Prop :=
  forall kst, KInvariant kst ->
  forall x y, ktr kst = [x ++ bef ++ y]%inhabited ->
  exists z, x = z ++ aft.

Definition valid_msg (m: msg) : Prop :=
  forall t, m <> BadTag t.

Ltac imm_tac_step :=
  match goal with
  | |- exists z, ?x = z ++ ?x =>
      exists nil; auto

  | H: nil = _ ++ _ :: _ |- _ =>
      apply app_cons_not_nil in H; contradiction

  | H: valid_msg (BadTag ?t) |- _ =>
      unfold valid_msg in H; edestruct H; eauto

  | H : inhabit_unpack ?tr _ = [_]%inhabited |- _ =>
      match tr with
      | ktr ?s =>
          destruct s; simpl in *
      | tr =>
          unfold tr in *; clear tr
      | tr =>
          destruct tr; simpl in *
      end

  | H: [_]%inhabited = [_]%inhabited |- _ =>
      apply pack_injective in H

  | H: _ :: _ = ?tr ++ _ |- _ =>
      destruct tr; simpl in *; inv H

  | H: ValidExchange _  _ |- _ =>
      inv H; simpl in *

  | |- exists z, ?a :: ?x = z ++ ?c =>
      let H := fresh "H" in
      let e := fresh "e" in
      cut (exists z, x = z ++ c);
        [ intro H; destruct H as [e H]; rewrite H; exists (a :: e); auto | ]

  | _ =>
      eauto
  end.

Ltac imm_tac :=
  repeat progress imm_tac_step.



Inductive ParamT : Set :=
  Str | Num | Fdesc | Chan.

Definition ParamTDenote (pt : ParamT) : Set :=
  match pt with
  | Str   => str
  | Num   => num
  | Fdesc => fdesc
  | Chan  => tchan
  end.

Inductive ParamPat (pt : ParamT) : Set :=
| PP_Any : ParamPat pt
| PP_Lit : ParamTDenote pt -> ParamPat pt
| PP_Var : nat -> ParamPat pt
.

Definition CtxKey : nat * ParamT -> Set :=
  fun key : nat * ParamT => ParamTDenote (snd key).

Definition Ctx : Set :=
  list (sigT CtxKey).

Definition EmptyCtx : Ctx :=
  nil.

Inductive ParamMatch (pt : ParamT) :
  Ctx -> ParamPat pt -> ParamTDenote pt -> Prop :=
| PM_Any :
  forall ctx p,
  ParamMatch pt ctx (PP_Any pt) p
| PM_Lit :
  forall ctx p,
  ParamMatch pt ctx (PP_Lit pt p) p
| PM_Var :
  forall id v ctx,
  In (existT CtxKey (id, pt) v) ctx ->
  ParamMatch pt ctx (PP_Var pt id) v
.

Section ContextDefs.

Variable ctx : Ctx.

Inductive MsgPat : Set :=
| MP_LoginReq : ParamPat Str -> MsgPat
| MP_LoginRes : ParamPat Num -> MsgPat
| MP_PubkeyReq : MsgPat
| MP_PubkeyRes : ParamPat Str -> MsgPat
| MP_KeysignReq : ParamPat Str -> MsgPat
| MP_KeysignRes : ParamPat Str -> MsgPat
| MP_CreatePtyerReq : MsgPat
| MP_CreatePtyerRes : ParamPat Fdesc -> ParamPat Fdesc -> MsgPat
| MP_SysLoginReq : ParamPat Str -> MsgPat
| MP_SysLoginRes : ParamPat Str -> ParamPat Num -> MsgPat
| MP_SysPubkeyReq : MsgPat
| MP_SysPubkeyRes : ParamPat Str -> MsgPat
| MP_SysKeysignReq : ParamPat Str -> MsgPat
| MP_SysKeysignRes : ParamPat Str -> MsgPat
| MP_SysCreatePtyerReq : ParamPat Str -> MsgPat
| MP_SysCreatePtyerRes : ParamPat Fdesc -> ParamPat Fdesc -> MsgPat
.

Inductive MsgMatch : MsgPat -> msg -> Prop :=
| MM_LoginReq :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_LoginReq pp0) (LoginReq p0)
| MM_LoginRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Num ctx pp0 p0 ->
  MsgMatch (MP_LoginRes pp0) (LoginRes p0)
| MM_PubkeyReq :
  ctx = ctx ->
  MsgMatch (MP_PubkeyReq) (PubkeyReq)
| MM_PubkeyRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_PubkeyRes pp0) (PubkeyRes p0)
| MM_KeysignReq :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_KeysignReq pp0) (KeysignReq p0)
| MM_KeysignRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_KeysignRes pp0) (KeysignRes p0)
| MM_CreatePtyerReq :
  ctx = ctx ->
  MsgMatch (MP_CreatePtyerReq) (CreatePtyerReq)
| MM_CreatePtyerRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Fdesc ctx pp0 p0 ->
  forall pp1 p1, ParamMatch Fdesc ctx pp1 p1 ->
  MsgMatch (MP_CreatePtyerRes pp0 pp1) (CreatePtyerRes p0 p1)
| MM_SysLoginReq :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_SysLoginReq pp0) (SysLoginReq p0)
| MM_SysLoginRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  forall pp1 p1, ParamMatch Num ctx pp1 p1 ->
  MsgMatch (MP_SysLoginRes pp0 pp1) (SysLoginRes p0 p1)
| MM_SysPubkeyReq :
  ctx = ctx ->
  MsgMatch (MP_SysPubkeyReq) (SysPubkeyReq)
| MM_SysPubkeyRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_SysPubkeyRes pp0) (SysPubkeyRes p0)
| MM_SysKeysignReq :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_SysKeysignReq pp0) (SysKeysignReq p0)
| MM_SysKeysignRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_SysKeysignRes pp0) (SysKeysignRes p0)
| MM_SysCreatePtyerReq :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Str ctx pp0 p0 ->
  MsgMatch (MP_SysCreatePtyerReq pp0) (SysCreatePtyerReq p0)
| MM_SysCreatePtyerRes :
  ctx = ctx ->
  forall pp0 p0, ParamMatch Fdesc ctx pp0 p0 ->
  forall pp1 p1, ParamMatch Fdesc ctx pp1 p1 ->
  MsgMatch (MP_SysCreatePtyerRes pp0 pp1) (SysCreatePtyerRes p0 p1)
.

(* TODO constrain chan in send / recv patterns *)

Inductive KActionPat : Set :=
| KAP_Any   : KActionPat
| KAP_KSend : ParamPat Chan -> MsgPat -> KActionPat
| KAP_KRecv : ParamPat Chan -> MsgPat -> KActionPat
.

Inductive KActionMatch : KActionPat -> KAction -> Prop :=
| KAM_Any :
  forall a,
  KActionMatch KAP_Any a
| KAM_KSend :
  forall cp c mp m,
  ParamMatch Chan ctx cp c ->
  MsgMatch mp m ->
  KActionMatch (KAP_KSend cp mp) (KSend c m)
| KAM_KRecv :
  forall cp c mp m,
  ParamMatch Chan ctx cp c ->
  MsgMatch mp m ->
  KActionMatch (KAP_KRecv cp mp) (KRecv c m)
.

Inductive KTracePat : Set :=
| KTP_Emp  : KTracePat
| KTP_Act  : KActionPat -> KTracePat
| KTP_NAct : KActionPat -> KTracePat
| KTP_Alt  : KTracePat -> KTracePat -> KTracePat
| KTP_And  : KTracePat -> KTracePat -> KTracePat
| KTP_Cat  : KTracePat -> KTracePat -> KTracePat
| KTP_Star : KTracePat -> KTracePat
| KTP_Ctx_ChanT : nat -> chan_type -> KTracePat
.

Inductive KTraceMatch : KTracePat -> KTrace -> Prop :=
| KTM_Emp :
  KTraceMatch KTP_Emp nil
| KTM_Act :
  forall kap a,
  KActionMatch kap a ->
  KTraceMatch (KTP_Act kap) (a :: nil)
| KTM_NAct :
  forall kap a,
  ~ KActionMatch kap a ->
  KTraceMatch (KTP_NAct kap) (a :: nil)
| KTM_Alt_l :
  forall p1 p2 t,
  KTraceMatch p1 t ->
  KTraceMatch (KTP_Alt p1 p2) t
| KTM_Alt_r :
  forall p1 p2 t,
  KTraceMatch p2 t ->
  KTraceMatch (KTP_Alt p1 p2) t
| KTM_And :
  forall p1 p2 t,
  KTraceMatch p1 t ->
  KTraceMatch p2 t ->
  KTraceMatch (KTP_And p1 p2) t
| KTM_Cat :
  forall p1 p2 t1 t2,
  KTraceMatch p1 t1 ->
  KTraceMatch p2 t2 ->
  KTraceMatch (KTP_Cat p1 p2) (t1 ++ t2)
| KTM_Star_0 :
  forall p,
  KTraceMatch (KTP_Star p) nil
| KTM_Star_N :
  forall p t1 t2,
  KTraceMatch p t1 ->
  KTraceMatch (KTP_Star p) t2 ->
  KTraceMatch (KTP_Star p) (t1 ++ t2)
| KTM_Ctx_ChanT :
  forall id ct c tr,
  In (existT CtxKey (id, Chan) c) ctx ->
  projT1 c = ct ->
  KTraceMatch (KTP_Ctx_ChanT id ct) tr
.

Lemma KTM_Star_app :
  forall p t1 t2,
  KTraceMatch (KTP_Star p) t1 ->
  KTraceMatch (KTP_Star p) t2 ->
  KTraceMatch (KTP_Star p) (t1 ++ t2).
Proof.
  intros. remember (KTP_Star p) as PAT.
  induction H; inv HeqPAT. auto.
  rewrite app_ass. constructor; auto.
Qed.

Lemma KTM_Cat_Empty :
  forall p tr,
  KTraceMatch p tr ->
  KTraceMatch (KTP_Cat KTP_Emp p) tr.
Proof.
  intros. replace tr with (nil ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Any :
  forall ka,
  KTraceMatch (KTP_Act KAP_Any) (ka :: nil).
Proof.
  repeat constructor; auto.
Qed.

Lemma KTM_AnyStar :
  forall tr,
  KTraceMatch (KTP_Star (KTP_Act KAP_Any)) tr.
Proof.
  induction tr. constructor.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_Act_cons :
  forall ap a t,
  KTraceMatch (KTP_Star (KTP_Act ap)) (a :: t) <->
  KActionMatch ap a /\ KTraceMatch (KTP_Star (KTP_Act ap)) t.
Proof.
  split; intros; inv H.
  inv H2. inv H1. auto.
  replace (a :: t) with ((a :: nil) ++ t) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_NAct_cons :
  forall ap a t,
  KTraceMatch (KTP_Star (KTP_NAct ap)) (a :: t) <->
  ~ KActionMatch ap a /\ KTraceMatch (KTP_Star (KTP_NAct ap)) t.
Proof.
  split; intros; inv H.
  inv H2. inv H1. auto.
  replace (a :: t) with ((a :: nil) ++ t) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_Act_app :
  forall ap t1 t2,
  KTraceMatch (KTP_Star (KTP_Act ap)) (t1 ++ t2) <->
  KTraceMatch (KTP_Star (KTP_Act ap)) t1 /\
  KTraceMatch (KTP_Star (KTP_Act ap)) t2.
Proof.
  split; intros.
  (* -> *)
  induction t1; simpl in *. repeat constructor; auto.
  apply KTM_Star_Act_cons in H; destruct H.
  apply IHt1 in H0; destruct H0.
  replace (a :: t1) with ((a :: nil) ++ t1) by auto.
  repeat constructor; auto.
  (* <- *)
  destruct H. apply KTM_Star_app; auto.
Qed.

Lemma KTM_Star_NAct_app :
  forall ap t1 t2,
  KTraceMatch (KTP_Star (KTP_NAct ap)) (t1 ++ t2) <->
  KTraceMatch (KTP_Star (KTP_NAct ap)) t1 /\
  KTraceMatch (KTP_Star (KTP_NAct ap)) t2.
Proof.
  split; intros.
  (* -> *)
  induction t1; simpl in *. repeat constructor; auto.
  apply KTM_Star_NAct_cons in H; destruct H.
  apply IHt1 in H0; destruct H0.
  replace (a :: t1) with ((a :: nil) ++ t1) by auto.
  repeat constructor; auto.
  (* <- *)
  destruct H. apply KTM_Star_app; auto.
Qed.

Definition KTP_Equiv (p1 p2 : KTracePat) : Prop :=
  forall tr, KTraceMatch p1 tr <-> KTraceMatch p2 tr.

Lemma star_swap :
  forall p1 p2,
  KTP_Equiv p1 p2 ->
  KTP_Equiv (KTP_Star p1) (KTP_Star p2).
Proof.
  unfold KTP_Equiv; split; intros.
  remember (KTP_Star p1) as PAT; induction H0; inv HeqPAT.
  constructor. apply H in H0_. constructor; auto.
  remember (KTP_Star p2) as PAT; induction H0; inv HeqPAT.
  constructor. apply H in H0_. constructor; auto.
Qed.

Lemma and_comm :
  forall p1 p2,
  KTP_Equiv
    (KTP_And p1 p2)
    (KTP_And p2 p1).
Proof.
  unfold KTP_Equiv; split; intro H; inv H;
    repeat constructor; auto.
Qed.

Lemma and_assoc :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_And p1 (KTP_And p2 p3))
    (KTP_And (KTP_And p1 p2) p3).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H4; repeat constructor; auto.
  inv H2; repeat constructor; auto.
Qed.

Lemma alt_comm :
  forall p1 p2,
  KTP_Equiv
    (KTP_Alt p1 p2)
    (KTP_Alt p2 p1).
Proof.
  unfold KTP_Equiv; split; intro H; inv H;
    solve [ apply KTM_Alt_l; auto
          | apply KTM_Alt_r; auto
          ].
Qed.

Lemma alt_assoc :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Alt p1 (KTP_Alt p2 p3))
    (KTP_Alt (KTP_Alt p1 p2) p3).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  apply KTM_Alt_l; apply KTM_Alt_l; auto.
  inv H3.
    apply KTM_Alt_l; apply KTM_Alt_r; auto.
    apply KTM_Alt_r; auto.
  inv H3.
    apply KTM_Alt_l; auto.
    apply KTM_Alt_r; apply KTM_Alt_l; auto.
  apply KTM_Alt_r; apply KTM_Alt_r; auto.
Qed.

Lemma distr_cat_alt_l :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Cat (KTP_Alt p1 p2) p3)
    (KTP_Alt (KTP_Cat p1 p3) (KTP_Cat p2 p3)).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H2.
    apply KTM_Alt_l; constructor; auto.
    apply KTM_Alt_r; constructor; auto.
  inv H3. constructor; auto. apply KTM_Alt_l; auto.
  inv H3. constructor; auto. apply KTM_Alt_r; auto.
Qed.

Lemma distr_cat_alt_r :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Cat p1 (KTP_Alt p2 p3))
    (KTP_Alt (KTP_Cat p1 p2) (KTP_Cat p1 p3)).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H4.
    apply KTM_Alt_l; constructor; auto.
    apply KTM_Alt_r; constructor; auto.
  inv H3. constructor; auto. apply KTM_Alt_l; auto.
  inv H3. constructor; auto. apply KTM_Alt_r; auto.
Qed.

Lemma distr_star_and_act_l :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And (KTP_Act a) p)) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_Act a)) (KTP_Star p)) tr.
Proof.
  intros. remember (KTP_Star (KTP_And (KTP_Act a) p)) as PAT.
  induction H; inv HeqPAT. repeat constructor.
  specialize (IHKTraceMatch2 (refl_equal _)).
  inv IHKTraceMatch2. inv H. repeat constructor; auto.
Qed.

Lemma distr_star_and_nact_l :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And (KTP_NAct a) p)) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_NAct a)) (KTP_Star p)) tr.
Proof.
  intros. remember (KTP_Star (KTP_And (KTP_NAct a) p)) as PAT.
  induction H; inv HeqPAT. repeat constructor.
  specialize (IHKTraceMatch2 (refl_equal _)).
  inv IHKTraceMatch2. inv H. repeat constructor; auto.
Qed.

Lemma distr_star_and_act_r :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And p (KTP_Act a))) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_Act a)) (KTP_Star p)) tr.
Proof.
  intros. apply distr_star_and_act_l.
  eapply star_swap; eauto. apply and_comm.
Qed.

Lemma distr_star_and_nact_r :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And p (KTP_NAct a))) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_NAct a)) (KTP_Star p)) tr.
Proof.
  intros. apply distr_star_and_nact_l.
  eapply star_swap; eauto. apply and_comm.
Qed.

Lemma distr_star_and_act2 :
  forall a1 a2,
  KTP_Equiv
    (KTP_Star (KTP_And (KTP_Act a1) (KTP_Act a2)))
    (KTP_And (KTP_Star (KTP_Act a1)) (KTP_Star (KTP_Act a2))).
Proof.
  unfold KTP_Equiv; split; intro H.
  apply distr_star_and_act_l; auto.
  (* <- *)
  inv H. induction tr. constructor.
  apply KTM_Star_Act_cons in H2; destruct H2.
  apply KTM_Star_Act_cons in H4; destruct H4.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma distr_star_and_nact2 :
  forall a1 a2,
  KTP_Equiv
    (KTP_Star (KTP_And (KTP_NAct a1) (KTP_NAct a2)))
    (KTP_And (KTP_Star (KTP_NAct a1)) (KTP_Star (KTP_NAct a2))).
Proof.
  unfold KTP_Equiv; split; intro H.
  apply distr_star_and_nact_l; auto.
  (* <- *)
  inv H. induction tr. constructor.
  apply KTM_Star_NAct_cons in H2; destruct H2.
  apply KTM_Star_NAct_cons in H4; destruct H4.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

End ContextDefs.

Inductive KTraceSpec : Set :=
| KTS_Pat  : KTracePat -> KTraceSpec
| KTS_NPat : KTracePat -> KTraceSpec
.

Inductive KTraceMatchSpec : KTraceSpec -> KTrace -> Prop :=
| KTMS_Pat :
  forall ctx p tr,
  KTraceMatch ctx p tr ->
  KTraceMatchSpec (KTS_Pat p) tr
| KTMS_NPat :
  forall p tr,
  (forall ctx, ~ KTraceMatch ctx p tr) ->
  KTraceMatchSpec (KTS_NPat p) tr
.

(*


(* TODO constrain chan in send / recv patterns *)

Inductive KActionPat : Set :=
| KAP_Any   : KActionPat
| KAP_KSend : MsgPat -> KActionPat
| KAP_KRecv : MsgPat -> KActionPat
.

Inductive KActionMatch : KActionPat -> KAction -> Prop :=
| KAM_Any :
  forall a,
  KActionMatch KAP_Any a
| KAM_KSend :
  forall mp c m,
  MsgMatch mp m ->
  KActionMatch (KAP_KSend mp) (KSend c m)
| KAM_KRecv :
  forall mp c m,
  MsgMatch mp m ->
  KActionMatch (KAP_KRecv mp) (KRecv c m)
.

Inductive KTracePat : Set :=
| KTP_Emp  : KTracePat
| KTP_Act  : KActionPat -> KTracePat
| KTP_NAct : KActionPat -> KTracePat
| KTP_Alt  : KTracePat -> KTracePat -> KTracePat
| KTP_And  : KTracePat -> KTracePat -> KTracePat
| KTP_Cat  : KTracePat -> KTracePat -> KTracePat
| KTP_Star : KTracePat -> KTracePat
.

Inductive KTraceMatch : KTracePat -> KTrace -> Prop :=
| KTM_Emp :
  KTraceMatch KTP_Emp nil
| KTM_Act :
  forall kap a,
  KActionMatch kap a ->
  KTraceMatch (KTP_Act kap) (a :: nil)
| KTM_NAct :
  forall kap a,
  ~ KActionMatch kap a ->
  KTraceMatch (KTP_NAct kap) (a :: nil)
| KTM_Alt_l :
  forall p1 p2 t,
  KTraceMatch p1 t ->
  KTraceMatch (KTP_Alt p1 p2) t
| KTM_Alt_r :
  forall p1 p2 t,
  KTraceMatch p2 t ->
  KTraceMatch (KTP_Alt p1 p2) t
| KTM_And :
  forall p1 p2 t,
  KTraceMatch p1 t ->
  KTraceMatch p2 t ->
  KTraceMatch (KTP_And p1 p2) t
| KTM_Cat :
  forall p1 p2 t1 t2,
  KTraceMatch p1 t1 ->
  KTraceMatch p2 t2 ->
  KTraceMatch (KTP_Cat p1 p2) (t1 ++ t2)
| KTM_Star_0 :
  forall p,
  KTraceMatch (KTP_Star p) nil
| KTM_Star_N :
  forall p t1 t2,
  KTraceMatch p t1 ->
  KTraceMatch (KTP_Star p) t2 ->
  KTraceMatch (KTP_Star p) (t1 ++ t2)
.

Inductive KTraceSpec : Set :=
| KTS_Pat  : KTracePat -> KTraceSpec
| KTS_NPat : KTracePat -> KTraceSpec
.

Inductive KTraceMatchSpec : KTraceSpec -> KTrace -> Prop :=
| KTMS_Pat :
  forall p tr,
  KTraceMatch p tr ->
  KTraceMatchSpec (KTS_Pat p) tr
| KTMS_NPat :
  forall p tr,
  ~ KTraceMatch p tr ->
  KTraceMatchSpec (KTS_NPat p) tr
.

Lemma KTM_Star_app :
  forall p t1 t2,
  KTraceMatch (KTP_Star p) t1 ->
  KTraceMatch (KTP_Star p) t2 ->
  KTraceMatch (KTP_Star p) (t1 ++ t2).
Proof.
  intros. remember (KTP_Star p) as PAT.
  induction H; inv HeqPAT. auto.
  rewrite app_ass. constructor; auto.
Qed.

Lemma KTM_Cat_Empty :
  forall p tr,
  KTraceMatch p tr ->
  KTraceMatch (KTP_Cat KTP_Emp p) tr.
Proof.
  intros. replace tr with (nil ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Any :
  forall ka,
  KTraceMatch (KTP_Act KAP_Any) (ka :: nil).
Proof.
  repeat constructor; auto.
Qed.

Lemma KTM_AnyStar :
  forall tr,
  KTraceMatch (KTP_Star (KTP_Act KAP_Any)) tr.
Proof.
  induction tr. constructor.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_Act_cons :
  forall ap a t,
  KTraceMatch (KTP_Star (KTP_Act ap)) (a :: t) <->
  KActionMatch ap a /\ KTraceMatch (KTP_Star (KTP_Act ap)) t.
Proof.
  split; intros; inv H.
  inv H2. inv H1. auto.
  replace (a :: t) with ((a :: nil) ++ t) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_NAct_cons :
  forall ap a t,
  KTraceMatch (KTP_Star (KTP_NAct ap)) (a :: t) <->
  ~ KActionMatch ap a /\ KTraceMatch (KTP_Star (KTP_NAct ap)) t.
Proof.
  split; intros; inv H.
  inv H2. inv H1. auto.
  replace (a :: t) with ((a :: nil) ++ t) by auto.
  repeat constructor; auto.
Qed.

Lemma KTM_Star_Act_app :
  forall ap t1 t2,
  KTraceMatch (KTP_Star (KTP_Act ap)) (t1 ++ t2) <->
  KTraceMatch (KTP_Star (KTP_Act ap)) t1 /\
  KTraceMatch (KTP_Star (KTP_Act ap)) t2.
Proof.
  split; intros.
  (* -> *)
  induction t1; simpl in *. repeat constructor; auto.
  apply KTM_Star_Act_cons in H; destruct H.
  apply IHt1 in H0; destruct H0.
  replace (a :: t1) with ((a :: nil) ++ t1) by auto.
  repeat constructor; auto.
  (* <- *)
  destruct H. apply KTM_Star_app; auto.
Qed.

Lemma KTM_Star_NAct_app :
  forall ap t1 t2,
  KTraceMatch (KTP_Star (KTP_NAct ap)) (t1 ++ t2) <->
  KTraceMatch (KTP_Star (KTP_NAct ap)) t1 /\
  KTraceMatch (KTP_Star (KTP_NAct ap)) t2.
Proof.
  split; intros.
  (* -> *)
  induction t1; simpl in *. repeat constructor; auto.
  apply KTM_Star_NAct_cons in H; destruct H.
  apply IHt1 in H0; destruct H0.
  replace (a :: t1) with ((a :: nil) ++ t1) by auto.
  repeat constructor; auto.
  (* <- *)
  destruct H. apply KTM_Star_app; auto.
Qed.

Definition KTP_Equiv (p1 p2 : KTracePat) : Prop :=
  forall tr, KTraceMatch p1 tr <-> KTraceMatch p2 tr.

Lemma star_swap :
  forall p1 p2,
  KTP_Equiv p1 p2 ->
  KTP_Equiv (KTP_Star p1) (KTP_Star p2).
Proof.
  unfold KTP_Equiv; split; intros.
  remember (KTP_Star p1) as PAT; induction H0; inv HeqPAT.
  constructor. apply H in H0_. constructor; auto.
  remember (KTP_Star p2) as PAT; induction H0; inv HeqPAT.
  constructor. apply H in H0_. constructor; auto.
Qed.

Lemma and_comm :
  forall p1 p2,
  KTP_Equiv
    (KTP_And p1 p2)
    (KTP_And p2 p1).
Proof.
  unfold KTP_Equiv; split; intro H; inv H;
    repeat constructor; auto.
Qed.

Lemma and_assoc :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_And p1 (KTP_And p2 p3))
    (KTP_And (KTP_And p1 p2) p3).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H4; repeat constructor; auto.
  inv H2; repeat constructor; auto.
Qed.

Lemma alt_comm :
  forall p1 p2,
  KTP_Equiv
    (KTP_Alt p1 p2)
    (KTP_Alt p2 p1).
Proof.
  unfold KTP_Equiv; split; intro H; inv H;
    solve [ apply KTM_Alt_l; auto
          | apply KTM_Alt_r; auto
          ].
Qed.

Lemma alt_assoc :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Alt p1 (KTP_Alt p2 p3))
    (KTP_Alt (KTP_Alt p1 p2) p3).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  apply KTM_Alt_l; apply KTM_Alt_l; auto.
  inv H3.
    apply KTM_Alt_l; apply KTM_Alt_r; auto.
    apply KTM_Alt_r; auto.
  inv H3.
    apply KTM_Alt_l; auto.
    apply KTM_Alt_r; apply KTM_Alt_l; auto.
  apply KTM_Alt_r; apply KTM_Alt_r; auto.
Qed.

Lemma distr_cat_alt_l :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Cat (KTP_Alt p1 p2) p3)
    (KTP_Alt (KTP_Cat p1 p3) (KTP_Cat p2 p3)).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H2.
    apply KTM_Alt_l; constructor; auto.
    apply KTM_Alt_r; constructor; auto.
  inv H3. constructor; auto. apply KTM_Alt_l; auto.
  inv H3. constructor; auto. apply KTM_Alt_r; auto.
Qed.

Lemma distr_cat_alt_r :
  forall p1 p2 p3,
  KTP_Equiv
    (KTP_Cat p1 (KTP_Alt p2 p3))
    (KTP_Alt (KTP_Cat p1 p2) (KTP_Cat p1 p3)).
Proof.
  unfold KTP_Equiv; split; intro H; inv H.
  inv H4.
    apply KTM_Alt_l; constructor; auto.
    apply KTM_Alt_r; constructor; auto.
  inv H3. constructor; auto. apply KTM_Alt_l; auto.
  inv H3. constructor; auto. apply KTM_Alt_r; auto.
Qed.

Lemma distr_star_and_act_l :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And (KTP_Act a) p)) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_Act a)) (KTP_Star p)) tr.
Proof.
  intros. remember (KTP_Star (KTP_And (KTP_Act a) p)) as PAT.
  induction H; inv HeqPAT. repeat constructor.
  specialize (IHKTraceMatch2 (refl_equal _)).
  inv IHKTraceMatch2. inv H. repeat constructor; auto.
Qed.

Lemma distr_star_and_nact_l :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And (KTP_NAct a) p)) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_NAct a)) (KTP_Star p)) tr.
Proof.
  intros. remember (KTP_Star (KTP_And (KTP_NAct a) p)) as PAT.
  induction H; inv HeqPAT. repeat constructor.
  specialize (IHKTraceMatch2 (refl_equal _)).
  inv IHKTraceMatch2. inv H. repeat constructor; auto.
Qed.

Lemma distr_star_and_act_r :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And p (KTP_Act a))) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_Act a)) (KTP_Star p)) tr.
Proof.
  intros. apply distr_star_and_act_l.
  eapply star_swap; eauto. apply and_comm.
Qed.

Lemma distr_star_and_nact_r :
  forall a p tr,
  KTraceMatch (KTP_Star (KTP_And p (KTP_NAct a))) tr ->
  KTraceMatch (KTP_And (KTP_Star (KTP_NAct a)) (KTP_Star p)) tr.
Proof.
  intros. apply distr_star_and_nact_l.
  eapply star_swap; eauto. apply and_comm.
Qed.

Lemma distr_star_and_act2 :
  forall a1 a2,
  KTP_Equiv
    (KTP_Star (KTP_And (KTP_Act a1) (KTP_Act a2)))
    (KTP_And (KTP_Star (KTP_Act a1)) (KTP_Star (KTP_Act a2))).
Proof.
  unfold KTP_Equiv; split; intro H.
  apply distr_star_and_act_l; auto.
  (* <- *)
  inv H. induction tr. constructor.
  apply KTM_Star_Act_cons in H2; destruct H2.
  apply KTM_Star_Act_cons in H4; destruct H4.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

Lemma distr_star_and_nact2 :
  forall a1 a2,
  KTP_Equiv
    (KTP_Star (KTP_And (KTP_NAct a1) (KTP_NAct a2)))
    (KTP_And (KTP_Star (KTP_NAct a1)) (KTP_Star (KTP_NAct a2))).
Proof.
  unfold KTP_Equiv; split; intro H.
  apply distr_star_and_nact_l; auto.
  (* <- *)
  inv H. induction tr. constructor.
  apply KTM_Star_NAct_cons in H2; destruct H2.
  apply KTM_Star_NAct_cons in H4; destruct H4.
  replace (a :: tr) with ((a :: nil) ++ tr) by auto.
  repeat constructor; auto.
Qed.

Ltac apply_ktm_false_hyp :=
  match goal with
  | [ H: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: _ -> KTraceMatch _ _ -> False |- _ ] => apply H
  | [ H: KTraceMatch _ _ -> False |- _ ] => apply H
  end.

Ltac ktm_basic :=
  repeat match goal with
  (* accept gifts from our ancestors *)
  | _ => assumption || discriminate || contradiction

  (* take low hanging fruit *)
  | [ _: KTraceMatch (KTP_Star ?p) ?t1
    , _: KTraceMatch (KTP_Star ?p) ?t2
      |- KTraceMatch (KTP_Star ?p) (?t1 ++ ?t2)     ] => apply KTM_Star_app
  | [ |- KTraceMatch (KTP_Star _) nil               ] => apply KTM_Star_0
  | [ |- KTraceMatch (KTP_Star (KTP_Act KAP_Any)) _ ] => apply KTM_AnyStar
  | [ |- KTraceMatch (KTP_Act KAP_Any) (_ :: nil)   ] => apply KTM_Any

  (* action matching goals *)
  | [ |- MsgMatch _ _ ] =>
    econstructor; eauto
  | [ |- KActionMatch _ _ ] =>
    econstructor; eauto
  | [ |- ~ KActionMatch _ _ ] =>
    let H := fresh in intro H; inv H

  (* take apart useful hypotheses *)
  | [ H: MsgMatch _                _ |- _ ] => inv H
  | [ H: KActionMatch _            _ |- _ ] => inv H
  | [ H: KTraceMatch KTP_Emp       _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_Act _)   _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_NAct _)  _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_Alt _ _) _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_And _ _) _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_Cat _ _) _ |- _ ] => inv H
  | [ H: KTraceMatchSpec _         _ |- _ ] => inv H
  | [ H: KTraceMatch (KTP_Star (KTP_Act _))  (_ :: _) |- _ ] =>
    apply KTM_Star_Act_cons in H; destruct H
  | [ H: KTraceMatch (KTP_Star (KTP_NAct _)) (_ :: _) |- _ ] =>
    apply KTM_Star_NAct_cons in H; destruct H
  | [ H: KTraceMatch (KTP_Star (KTP_And (KTP_Act _)  (KTP_Act _)))  _ |- _ ] =>
    apply distr_star_and_act2 in H
  | [ H: KTraceMatch (KTP_Star (KTP_And (KTP_NAct _) (KTP_NAct _))) _ |- _ ] =>
    apply distr_star_and_nact2 in H

  (* canonicalize *)
  | [ |- KTraceMatch (KTP_Cat KTP_Emp _)       _ ] => apply KTM_Cat_Empty
  | [ |- KTraceMatch (KTP_Cat (KTP_Alt _ _) _) _ ] => apply distr_cat_alt_l
  | [ |- KTraceMatch (KTP_Cat _ (KTP_Alt _ _)) _ ] => apply distr_cat_alt_r
  | [ |- KTraceMatch (KTP_Star (KTP_And (KTP_Act _)  (KTP_Act _)))  _ ] =>
    apply distr_star_and_act2
  | [ |- KTraceMatch (KTP_Star (KTP_And (KTP_NAct _) (KTP_NAct _))) _ ] =>
    apply distr_star_and_nact2

  (* get the party started *)
  | [ |- KTraceMatchSpec (KTS_Pat  _) _ ] => constructor
  | [ |- KTraceMatchSpec (KTS_NPat _) _ ] => constructor; intro
  end.

Ltac ktm_solve :=
  ktm_basic;
  match goal with
  (* fail on obviously impossible goals *)
  | [ |- KTraceMatch KTP_Emp (_ :: _) ] => fail 1
  | [ |- KTraceMatch (KTP_Act  _) nil ] => fail 1
  | [ |- KTraceMatch (KTP_NAct _) nil ] => fail 1

  (* On KTP_Alt goals, constructor will alway hit KTM_Alt_l
   * and stop, so we have to explicitly try KTM_Alt_r after.
   *)
  | _ => constructor; ktm_solve
  | _ => apply KTM_Alt_r; ktm_solve

  (* guide goals derived from KTS_NPat or neg search *)
  | [ H: ~ KTraceMatch _ _  |- False ] => apply H; ktm_solve
  | [ H: ~ KActionMatch _ _ |- _     ] => destruct H; ktm_solve
  | [ H: ?l ++ _ = nil      |- _     ] => destruct l; inv H; ktm_solve
  | [ H: ?l ++ _ = _ :: _   |- _     ] => destruct l; inv H; ktm_solve
  | _ => apply_ktm_false_hyp; ktm_solve

  (* try different list groupings *)
  | _ =>
    rewrite app_comm_cons; ktm_solve
  | [ |- KTraceMatch _ (?a :: ?l) ] =>
    replace (a :: l) with (nil ++ a :: l) by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?a9 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?a8 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?a7 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?a4 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: a4 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: a4 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?a3 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: a3 :: t)
       with ((a0 :: a1 :: a2 :: a3 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?a2 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: t)
       with ((a0 :: a1 :: a2 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?a1 :: ?t) ] =>
    replace (a0 :: a1 :: t)
       with ((a0 :: a1 :: nil) ++ t)
         by auto; ktm_solve
  | [ |- KTraceMatch _ (?a0 :: ?t) ] =>
    replace (a0 :: t)
       with ((a0 :: nil) ++ t)
         by auto; ktm_solve

  (* did not solve, bad search path *)
  | _ => fail 1
  end.

Ltac ktm :=
  ktm_basic; try ktm_solve.

Ltac and_match_hyps :=
  repeat match goal with
  | [ H1: KTraceMatch ?p1 ?t
    , H2: KTraceMatch ?p2 ?t |- _ ] =>
    assert (KTraceMatch (KTP_And p1 p2) t) by (constructor; auto);
    clear H1 H2
  end.

Ltac fold_kstate s :=
  fold (Kernel.components s) in *;
  fold (Kernel.ktr s) in *;
    fold (Kernel.system s) in *;
  fold (Kernel.slave s) in *;
  fold (Kernel.logincnt s) in *;
  fold (Kernel.loginsucceded s) in *;
  fold (Kernel.username s) in *;
  idtac.

Ltac revert_when_hyps :=
  repeat match goal with
  | [ H: nat_of_num _ = _ |- _ ] => revert H
  end.

Ltac prep_neg_search :=
  and_match_hyps;
  match goal with
  | [ H1: KInvariant ?s
    , H2: KTraceMatch ?p ?k |- _ ] =>
    (* set up goal *)
    cut False; [contradiction|];
    revert H2; revert_when_hyps; fold_kstate s;
    (* package kstate *)
    let S := fresh "S" in
    remember s as S;
    cut (ktr S = ktr s); [| subst; auto];
    simpl (ktr s); generalize k;
    assert (KInvariant S) by (subst; auto);
    (* remove junk *)
    repeat match goal with
    | [ S: kstate, H: KInvariant S, X: _ |- _ ] => clear X
    end;
    repeat match goal with
    | [ H: _ |- _ ] => revert H
    end
  end.

Ltac ktmatch_step :=
  induction 1; [ | |
    match goal with
    | H: ValidExchange _ _ |- _ => inv H
    end
  ];
  simpl; intros; uninhabit; ktm;
  prep_neg_search.

Ltac ktmatch :=
  repeat ktmatch_step.

*)

Ltac ktm_group_acts ctac :=
  match goal with
  | _ =>
    rewrite app_comm_cons; ctac
  | [ |- KTraceMatch _ _ (?a :: ?l) ] =>
    replace (a :: l)
       with (nil ++ a :: l)
         by auto; ctac
  | [ |- KTraceMatch _ _ (?a0 :: ?a1 :: ?a2 :: ?t) ] =>
    replace (a0 :: a1 :: a2 :: t)
       with ((a0 :: a1 :: a2 :: nil) ++ t)
         by auto; ctac
  | [ |- KTraceMatch _ _ (?a0 :: ?a1 :: ?t) ] =>
    replace (a0 :: a1 :: t)
       with ((a0 :: a1 :: nil) ++ t)
         by auto; ctac
  | [ |- KTraceMatch _ _ (?a0 :: ?t) ] =>
    replace (a0 :: t)
       with ((a0 :: nil) ++ t)
         by auto; ctac
  end.

Ltac ktm_inv_hyps :=
  repeat match goal with
  | [ H: ParamMatch _ _ _ _ |- _ ] => inv H
  | [ H: MsgMatch     _ _ _ |- _ ] => inv H
  | [ H: KActionMatch _ _ _ |- _ ] => inv H
  | [ H: KTraceMatch _ ?p _ |- _ ] =>
    match p with
    | KTP_Star _ => fail 1
    | _ => inv H
    end
  | [ H: ?l ++ _ = nil    |- _ ] => destruct l; inv H
  | [ H: ?l ++ _ = _ :: _ |- _ ] => destruct l; inv H
  | [ H: KTraceMatch _ (KTP_Star (KTP_Act _))  (_ :: _) |- _ ] =>
    apply KTM_Star_Act_cons in H; destruct H
  | [ H: KTraceMatch _ (KTP_Star (KTP_NAct _)) (_ :: _) |- _ ] =>
    apply KTM_Star_NAct_cons in H; destruct H
  end.

Ltac ktm_search := auto;
  match goal with
  | _ =>
    discriminate
  | _ =>
    contradiction
  | [ |- ~ KActionMatch _ _ _ ] =>
    let H := fresh in
    intro H; ktm_inv_hyps; fail
  | [ H: ~ KActionMatch _ _ _ |- False ] =>
    apply H; ktm_search
  | _ =>
    constructor; ktm_search
  | _ =>
    apply KTM_Alt_r; ktm_search
  | _ =>
    ktm_group_acts ktm_search
  end.

Ltac ktm_pick_ctx :=
  repeat match goal with
  | [ H: KTraceMatchSpec _ _ |- _ ] =>
    inv H
  | [ H: KTraceMatch ?ctx _ _ |- KTraceMatchSpec (KTS_Pat _) _ ] =>
    apply (KTMS_Pat ctx _ _)
  | [ |- KTraceMatchSpec (KTS_Pat _) _ ] =>
    apply (KTMS_Pat nil _ _)
  | [ |- KTraceMatchSpec (KTS_NPat _) _ ] =>
    let ctx := fresh "ctx" in
    let Hm  := fresh "Hm" in
    constructor; intros ctx Hm
  | [ ctx: Ctx, H: forall ctx, ~ KTraceMatch _ _ _ |- False ] =>
    specialize (H ctx); destruct H

  (* these arise from recursing on a negative case *)
  | [ H: _ -> KTraceMatchSpec ?p ?tr |- False ] =>
    cut (KTraceMatchSpec p tr);
    [let HX := fresh in intro HX; inv HX | auto];
    clear H
  end.

Ltac ktm_start :=
  match goal with
  | [ |- forall kst, KInvariant kst -> ?P ] =>
    induction 1; [ | |
      match goal with
      | [ H: ValidExchange _ _ |- _ ] => inv H
      end
    ];
    simpl; intros; uninhabit
  end.

Ltac fold_kstate s :=
  fold (Kernel.components s) in *;
  fold (Kernel.ktr s) in *;
    fold (Kernel.system s) in *;
  fold (Kernel.slave s) in *;
  fold (Kernel.logincnt s) in *;
  fold (Kernel.loginsucceded s) in *;
  fold (Kernel.username s) in *;
  idtac.

Ltac ktm_recombine_ktm_hyps :=
  repeat match goal with
  | [ H1: KTraceMatch ?ctx ?p1 ?t
    , H2: KTraceMatch ?ctx ?p2 ?t |- _ ] =>
    assert (KTraceMatch ctx (KTP_And p1 p2) t) by (constructor; auto);
    clear H1 H2
  end.

Ltac ktm_save_when_hyps :=
  repeat match goal with
  | [ H: nat_of_num _ = _ |- _ ] => revert H
  end.

Ltac ktm_setup_neg_search :=
  ktm_recombine_ktm_hyps;
  match goal with
  | [ H1: KInvariant ?s
    , H2: KTraceMatch _ ?p ?tr |- _ ] =>
    (* set up negated goal *)
    cut (KTraceMatchSpec (KTS_NPat p) tr); [
      let H := fresh in intro H; inv H;
      match goal with
      | [ HX: forall ctx, ~ KTraceMatch ctx ?p ?tr |- _ ] =>
        apply HX in H2; contradiction
      end
    |];
    ktm_save_when_hyps; fold_kstate s;
    (* package kstate *)
    let S := fresh "S" in remember s as S;
    cut (ktr S = ktr s); [| subst; auto];
    simpl (ktr s); generalize tr;
    assert (KInvariant S) by (subst; auto);
    (* clean up context *)
    repeat match goal with
    | [ S: kstate, H: KInvariant S, X: _ |- _ ] => clear X
    end;
    repeat match goal with
    | [ H: _ |- _ ] => revert H
    end
  end.

Ltac ktm :=
  ktm_start;
  ktm_pick_ctx;
  ktm_inv_hyps;
  try ktm_search;
  ktm_setup_neg_search;
  ktm.
 
