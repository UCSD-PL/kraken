Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexHVec.
Require Import ReflexVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import List.
Require Import NIExists.

Require Import Coq.Logic.Eqdep.
Require Import Sumbool.

Section Prune.

Context {NB_MSG : nat}.
Variable PAYD     : vvdesc NB_MSG.
Variable COMPT    : Set.
Variable COMPTDEC : forall (x y : COMPT), decide (x = y).
Variable COMPS    : COMPT -> compd.
Variable IENVD    : vcdesc COMPT.
Variable KSTD     : vcdesc COMPT.
Definition comp := comp COMPT COMPS.
Definition cmd := Reflex.cmd PAYD COMPT COMPS KSTD.
Definition KTrace := KTrace PAYD COMPT COMPS.
Definition KAction := KAction PAYD COMPT COMPS.
Definition kstate := kstate PAYD COMPT COMPS KSTD.
Definition ktr := ktr PAYD COMPT COMPS KSTD.
Definition Nop := Reflex.Nop PAYD COMPT COMPS KSTD.
Definition Seq := Reflex.Seq PAYD COMPT COMPS KSTD.
Definition Send := Reflex.Send PAYD COMPT COMPS KSTD.
Definition StUpd := Reflex.StUpd PAYD COMPT COMPS KSTD.
Definition Spawn := Reflex.Spawn PAYD COMPT COMPS KSTD.
Definition Call := Reflex.Call PAYD COMPT COMPS KSTD.
Definition Ite := Reflex.Ite PAYD COMPT COMPS KSTD.
Definition hdlr_term := Reflex.hdlr_term PAYD COMPT COMPS KSTD.
Definition base_term := Reflex.base_term COMPT.
Definition match_comp := Reflex.match_comp COMPT COMPTDEC COMPS.
Definition elt_match := Reflex.elt_match COMPT COMPS.

Definition locals_eq (envd:vcdesc COMPT)
  (env1 env2 : sdenote_vcdesc COMPT COMPS envd)
  (lblr : fin (projT1 envd) -> bool) :=
  shvec_erase _ lblr _ env1 = shvec_erase _ lblr _ env2.

Definition ve_st c m envd cmd i s :=
    hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m
    envd s cmd i.

Definition base_term_ok_high envd d (t:base_term envd d) llblr :=
  match t with
  | SLit _ => true
  | NLit _ => true
  | Var i  => llblr i
  | _      => false
  end.

Fixpoint hdlr_term_ok_high ct mt envd c (t:hdlr_term ct mt envd c) vlblr llblr :=
  match t with
  | Base _ b    => base_term_ok_high _ _ b llblr
  | MVar _      => true
  | StVar i     => vlblr i
  | CComp       => true
  | CConf _ _ t => hdlr_term_ok_high _ _ _ _ t vlblr llblr
  end.

Fixpoint hdlr_expr_ok_high ct mt envd c
  (e:expr COMPT (hdlr_term ct mt) envd c) vlblr llblr :=
  match e with
  | Term _ t => hdlr_term_ok_high _ _ _ _ t vlblr llblr
  | UnOp _ _ _ e' => hdlr_expr_ok_high _ _ _ _ e' vlblr llblr
  | BinOp _ _ _ _ e1 e2 => andb (hdlr_expr_ok_high _ _ _ _ e1 vlblr llblr)
    (hdlr_expr_ok_high _ _ _ _ e2 vlblr llblr)
  end.

Definition expr_list_ok_high ct mt envd c
  (es:list (expr COMPT (hdlr_term ct mt) envd c)) vlblr llblr :=
  fold_right (fun e => andb
    (hdlr_expr_ok_high ct mt envd c e vlblr llblr)) true es.

Fixpoint pl_expr_ok_high ct mt envd n vd
  (ple:payload_expr' COMPT (hdlr_term ct mt) envd n vd) vlblr llblr :=
  match n as _n return
    forall (_vd:vdesc' _n) (ple:payload_expr' COMPT (hdlr_term ct mt) envd _n _vd), _
  with
  | O => fun _ _ => true
  | S n' => fun vd =>
    match vd as _vd return
      payload_expr' COMPT (hdlr_term ct mt) envd (S n') _vd -> _
    with
    | (vd0, vd') =>
      fun ple =>
        andb (hdlr_expr_ok_high ct mt envd _ (fst ple) vlblr llblr)
          (pl_expr_ok_high ct mt envd n' _ (snd ple) vlblr llblr)
    end
  end vd ple.

Fixpoint get_writes envd term (cmd:cmd term envd) :=
  match cmd in Reflex.cmd _ _ _ _ _ _envd return
    fin (projT1 _envd) -> bool
  with
  | Reflex.Seq _ cmd1 cmd2 =>
    fun i => andb (get_writes _ _ cmd1 i)
      (get_writes _ _ cmd2 i)
  | Reflex.Ite _ _ cmd1 cmd2 =>
    fun i => andb (get_writes _ _ cmd1 i)
      (get_writes _ _ cmd2 i)
  | Reflex.Spawn _ _ _ i' _ =>
    fun i => if fin_eq_dec i i' then false else true
  | Reflex.Call _ _ _ i' _ =>
    fun i => if fin_eq_dec i i' then false else true
  | Reflex.CompLkup _ _ cmd1 cmd2 =>
    fun i => andb (get_writes _ _ cmd1 (lift_fin i))
      (get_writes _ _ cmd2 i)
  | _ =>
    fun _ => true
  end.

Definition cp_incl cp1 cp2 :=
  forall c, implb (match_comp cp1 c)
    (match_comp cp2 c) = true.

Definition elt_incl d oelt1 oelt2 :=
  forall elt,
    implb (elt_match d elt oelt1)
    (elt_match d elt oelt2) = true.

Lemma desc_2 : forall (d:desc),
  ex (fun s1:s[[d]] => ex (fun s2:s[[d]] => s1 <> s2)).
Proof.
  destruct d.
    exists FALSE. exists TRUE. discriminate.
    Local Transparent str_of_string.
    exists (str_of_string ""). exists (str_of_string "a").
    discriminate.
    exists FALSE. exists TRUE. discriminate.
Qed.

Lemma desc_neq : forall (d:desc) (s:s[[d]]),
  exists s', s <> s'.
Proof.
  intros d s. pose proof (desc_2 d).
  destruct H. destruct H.
  destruct d.
    destruct (num_eq s x).
      exists x0. congruence.
      exists x. auto.

    destruct (str_eq s x).
      exists x0. congruence.
      exists x. auto.

    destruct (fd_eq s x).
      exists x0. congruence.
      exists x. auto.
Qed.

Lemma elt_incl_iff : forall d oelt1 oelt2,
  elt_incl d oelt1 oelt2 <->
  oelt2 = None \/ oelt1 = oelt2.
Proof.
  intros d oelt1 oelt2.
  split.
    intro Hincl. destruct oelt2.
      right. unfold elt_incl, elt_match in Hincl. simpl in Hincl.
      destruct oelt1.
        destruct d; specialize (Hincl s0); simpl in *;
          repeat match goal with
                 | [ _ : context[ if ?e then _ else _ ] |- _ ]
                   => destruct e
                 end; try solve [subst s; auto | discriminate |
                   specialize (n (Logic.eq_refl _)); contradiction].

        pose proof (desc_neq d s). destruct H.
        specialize (Hincl x). destruct d;
        match goal with
        | [ _ : context[ if ?e then _ else _ ] |- _ ]
          => destruct e
        end; try discriminate; try contradiction.

      left. auto.

    intro H. destruct H.
      subst oelt2. unfold elt_incl. simpl.
      intros. unfold implb. destruct (elt_match d elt oelt1); auto.

      subst oelt1. unfold elt_incl. simpl. intros.
      unfold implb. destruct (elt_match d elt oelt2); auto.
Qed.

Definition elt_incl_dec d oelt1 oelt2 :
  decide (elt_incl d oelt1 oelt2).
Proof.
  destruct oelt2.
    destruct oelt1.
    destruct d.
      destruct (num_eq s0 s);
        [left; subst s; apply elt_incl_iff; auto
          | right; intro H; apply elt_incl_iff in H;
            destruct H; try inversion H; contradiction].
      destruct (str_eq s0 s);
        [left; subst s; apply elt_incl_iff; auto
          | right; intro H; apply elt_incl_iff in H;
            destruct H; try inversion H; contradiction].
      destruct (fd_eq s0 s);
        [left; subst s; apply elt_incl_iff; auto
          | right; intro H; apply elt_incl_iff in H;
            destruct H; try inversion H; contradiction].

    right. intro H. apply elt_incl_iff in H. destruct H; discriminate.

    left. apply elt_incl_iff. auto.
Qed.

Definition default_desc (d:desc) : s[[d]] :=
match d with
| num_d => FALSE
| str_d => nil
| fd_d => devnull
end.

Definition default_desc_match (d:desc) (oelt:sdenote_desc_conc_pat d)
  : s[[d]] :=
match oelt with
| Some e => e
| None => default_desc d
end.

Lemma default_desc_match_ok : forall d oelt,
  elt_match d (default_desc_match d oelt) oelt = true.
Proof.
  intros d oelt.
  destruct oelt; auto.
  simpl. destruct d;
  match goal with
  |- context [ if ?e then _ else _ ]
    => destruct e
  end; auto.
Qed.

Definition non_match_vdesc n (vd:svec desc n) vdp :
  sig (fun v:s[[vd]] => shvec_match vd sdenote_desc sdenote_desc_conc_pat elt_match v vdp = true).
Proof.
  induction n.
    exact (exist _ tt (Logic.eq_refl _)).

    destruct vd as [d vd']. destruct vdp as [od vdp']. simpl in *.
    specialize (IHn vd' vdp'). destruct IHn.
    refine (exist _ (default_desc_match d od, x) _).
    rewrite default_desc_match_ok; auto.
Qed.

Definition cfgp_incl (cfgd:vdesc) cfgp1 cfgp2 :=
  forall cfg, implb
    (shvec_match (projT2 cfgd)
      sdenote_desc sdenote_desc_conc_pat elt_match
      cfg cfgp1)
    (shvec_match (projT2 cfgd)
      sdenote_desc sdenote_desc_conc_pat elt_match
      cfg cfgp2) = true.

Definition cfgp_incl_dec (cfgd:vdesc) cfgp1 cfgp2 :
  decide (cfgp_incl cfgd cfgp1 cfgp2).
Proof.
  destruct cfgd as [n cfgd]. unfold cfgp_incl.
  induction n.
    auto.

    simpl in *. destruct cfgd as [? cfgd'].
    destruct cfgp1 as [oelt1 cfgp1']. destruct cfgp2 as [oelt2 cfgp2'].
    specialize (IHn cfgd' cfgp1' cfgp2').
    destruct (elt_incl_dec d oelt1 oelt2).
      destruct IHn.
        left. intro cfg. destruct cfg as [elt cfg'].
        specialize (e elt).
        destruct (elt_match d elt oelt1).
          destruct (elt_match d elt oelt2); try discriminate.
          simpl. auto.

          auto.

        right. intro.

contradict n0. intro cfg.
specialize (H (default_desc_match d oelt1, cfg)).
specialize (e (default_desc_match d oelt1)). simpl in *.
rewrite default_desc_match_ok in *. simpl in *.
rewrite e in *. simpl in *. auto.

right. intro. contradict n0.
unfold elt_incl. intro elt.

pose proof (non_match_vdesc n cfgd' cfgp1') as rest.
destruct rest as [rest Hrest].
specialize (H (elt, rest)). simpl in *. rewrite Hrest in H.
simpl in *. destruct (elt_match d elt oelt1); auto.
simpl in *. destruct (elt_match d elt oelt2); auto.
Defined.

Definition cp_incl_dec cp1 cp2 : decide (cp_incl cp1 cp2).
Proof.
  destruct cp1 as [ct1 cfg1]; destruct cp2 as [ct2 cfg2].
  destruct (COMPTDEC ct1 ct2).
    subst ct1.
    destruct (cfgp_incl_dec _ cfg1 cfg2).
      left. unfold cp_incl, match_comp, Reflex.match_comp, match_comp_pf.
      simpl. intro cp.
      destruct (COMPTDEC (comp_type COMPT COMPS cp) ct2); auto. destruct e.
      specialize (c (comp_conf _ _ cp)). unfold elt_match in *.
      destruct (shvec_match
              (projT2 (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS cp)))
              sdenote_desc sdenote_desc_conc_pat (Reflex.elt_match COMPT COMPS)
              (comp_conf COMPT COMPS cp) cfg1);
      destruct (shvec_match
              (projT2 (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS cp)))
              sdenote_desc sdenote_desc_conc_pat (Reflex.elt_match COMPT COMPS)
              (comp_conf COMPT COMPS cp) cfg2); auto.

      right. intro. contradict n. intro cfg. unfold cp_incl in *.
      specialize (H {|comp_type:=ct2; comp_fd:=devnull; comp_conf:=cfg|}).
      unfold match_comp, Reflex.match_comp, match_comp_pf in *. simpl in *.
      destruct (COMPTDEC ct2 ct2); auto.
      rewrite UIP_refl with (p:=e) in *. unfold elt_match in *.
      destruct (shvec_match (projT2 (comp_conf_desc COMPT COMPS ct2))
                 sdenote_desc sdenote_desc_conc_pat
                 (Reflex.elt_match COMPT COMPS) cfg cfg1);
      destruct (shvec_match (projT2 (comp_conf_desc COMPT COMPS ct2))
                 sdenote_desc sdenote_desc_conc_pat
                 (Reflex.elt_match COMPT COMPS) cfg cfg2); auto.

      right. intro.
      pose proof (non_match_vdesc _ _ cfg1) as Hmatch.
      destruct Hmatch as [v Hv].
      specialize (H {|comp_type:=ct1;
        comp_fd:=devnull;
        comp_conf:=v|}).
      unfold match_comp, Reflex.match_comp, match_comp_pf in *.
      simpl in *. destruct (COMPTDEC ct1 ct2); try contradiction.
      destruct (COMPTDEC ct1 ct1).
      rewrite UIP_refl with (p:=e) in *. unfold elt_match in *.
      rewrite Hv in *. discriminate.
      contradict n1. auto.
Qed.

(*Definition high_cp_dec cp clblr :
  decide (high_comp_pat COMPT COMPTDEC COMPS cp
    (lblr_match_comp COMPT COMPTDEC COMPS clblr)).
Proof.
  induction clblr.
    left. unfold high_comp_pat. intros. simpl. auto.

    destruct IHclblr.
      left. unfold high_comp_pat. intros c Hmatch.
      specialize (h c Hmatch). unfold lblr_match_comp in *.
      destruct clblr. simpl in *. auto. simpl in *.
      rewrite h. auto.

      destruct (cp_incl_dec cp a).
        left. unfold high_comp_pat. intros comp Hmatch.
        specialize (c comp). unfold match_comp, NIExists.match_comp in *. rewrite Hmatch in c.
        simpl in *. unfold NIExists.match_comp. rewrite c. rewrite Bool.orb_true_r. auto.

        right. intro. unfold high_comp_pat in *.
      admit.
Qed.*)

Fixpoint get_llblr ct mt envd cmd vlblr llblr :=
  match cmd in Reflex.cmd _ _ _ _ _ _envd return
    (fin (projT1 _envd) -> bool) -> _
  with
  | Reflex.Seq _ cmd1 cmd2 => fun llblr =>
    let llblr1 := get_llblr ct mt _ cmd1 vlblr llblr in
    get_llblr ct mt _ cmd2 vlblr llblr1
  | Reflex.Ite envd e cmd1 cmd2 => fun llblr =>
    if hdlr_expr_ok_high ct mt envd _ e vlblr llblr
    then fun i => andb (get_llblr ct mt _ cmd1 vlblr llblr i)
      (get_llblr ct mt _ cmd2 vlblr llblr i)
    else fun i => andb (get_writes _ _ cmd1 i) (get_writes _ _ cmd2 i)
  | Reflex.CompLkup _ _ cmd1 cmd2 => fun _ =>
    fun i => andb (get_writes _ _ cmd1 (lift_fin i)) (get_writes _ _ cmd2 i)
  | Reflex.Spawn _ t e i _ => fun llblr =>
    if pl_expr_ok_high ct mt _ _ _ e vlblr llblr
    then fun i' =>
      if fin_eq_dec i i'
      then true
      else llblr i'
    else fun i' =>
      if fin_eq_dec i i'
      then false
      else llblr i'
  | _       => fun llblr => llblr
  end llblr.

(*Fixpoint get_candidate_pats clblr ct :
  list (shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct)))) :=
  match clblr with
  | nil => nil
  | a::clblr' =>
    match COMPTDEC ct (conc_pat_type _ COMPS a) with
    | left EQ =>
      match EQ in _ = _ct return
        shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS _ct))) -> _
      with
      | Logic.eq_refl => fun cfg0 =>
        cfg0::get_candidate_pats clblr' ct
      end (conc_pat_conf _ COMPS a)
    | right _ => get_candidate_pats clblr' ct
    end
  end.

Definition desc_val_eq {d:desc}
  : forall (e1 e2:s[[d]]), decide (e1 = e2) :=
  match d with
  | num_d => num_eq
  | str_d => str_eq
  | fd_d  => fd_eq
  end.

Definition merge_desc_pats (d:desc) (o1 o2:option s[[d]])
  : option s[[d]] :=
  match o1 with
  | Some e1 =>
    match o2 with
    | Some e2 => if desc_val_eq e1 e2
                 then Some e1
                 else None
    | None    => None
    end
  | None    => None
  end.

Fixpoint merge_cfgps n :
  forall (vd:svec desc n), shvec sdenote_desc_conc_pat vd ->
      shvec sdenote_desc_conc_pat vd -> shvec sdenote_desc_conc_pat vd :=
  match n as _n return
    forall (vd:svec desc _n), shvec sdenote_desc_conc_pat vd ->
      shvec sdenote_desc_conc_pat vd -> shvec sdenote_desc_conc_pat vd
  with
  | O => fun _ _ _ => tt
  | S n' => fun vd =>
    match vd as _vd return
      shvec (n:=S n') sdenote_desc_conc_pat _vd ->
      shvec (n:=S n') sdenote_desc_conc_pat _vd ->
      shvec (n:=S n') sdenote_desc_conc_pat _vd
    with
    | (vd0, vd') => fun cfgp1 cfgp2 =>
      (merge_desc_pats vd0 (fst cfgp1) (fst cfgp2), merge_cfgps n' vd' (snd cfgp1) (snd cfgp2))
    end
  end.

Definition merge_all_cfgps ct cfgps cfgp0 :=
  fold_right (merge_cfgps _ (projT2 (compd_conf (COMPS ct))))
  cfgp0 cfgps.
*)
(*Definition get_ccomp_vals ct cfgps cfgp0 :=
  {| conc_pat_type:=ct
   ; conc_pat_conf:=fold_right
       (merge_cfgps _ (projT2 (compd_conf (COMPS ct))))
       cfgp0 cfgps |}.*)
(*
Lemma compcd_inj : forall ct ct',
  Comp COMPT ct = Comp COMPT ct' ->
  ct = ct'.
Proof.
  intros. injection H. auto.
Qed.
*)

Definition peval_hdlr_term' {cd envd} ct mt (t : hdlr_term ct mt envd cd)
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
  destruct t.
  exact None.
  exact None.
  inversion t.
  exact None.
  subst. exact (shvec_ith _ _ v i).
  exact None.
  exact None.
  exact None.
Defined.

Definition uncomp a b : Comp COMPT a = Comp COMPT b -> a = b.
Proof.
  inversion 1. reflexivity.
Defined.

Definition peval_hdlr_term {cd envd} ct mt (t : hdlr_term ct mt envd cd)
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
refine (
  match t in Reflex.hdlr_term _ _ _ _ _ _ _ d return
    option (sdenote_cdesc COMPT COMPS d)
  with
  | Base _ _ => None
  | CComp => None
  | CConf ct i t' =>
    match t' in Reflex.hdlr_term _ _ _ _ _ _ _ d return
      d = Comp COMPT ct ->
      option (sdenote_cdesc COMPT COMPS
        (Desc COMPT (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct)) i)))
    with
    | Base d b => fun _ => None
    | CComp => fun EQ =>
      shvec_ith _ _
                match uncomp _ _ EQ in _ = _ct return
                  shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS _ct)))
                with eq_refl => v end
                i
    | CConf ct' i t' => fun _ => None
    | MVar i => fun _ => None
    | StVar i => fun _ => None
    end (eq_refl _)
  | MVar i => None
  | StVar i => None
  end
).
Defined.

Require Import Program.

Lemma peval_hdlr_term_sound : forall cd envd ct mt
  (t:hdlr_term ct mt envd cd) cfgp v cfg f pl,
  peval_hdlr_term ct mt t cfgp = Some v ->
  (forall i v,
    shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
    Some v ->
    shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
  (forall st env,
    eval_hdlr_term PAYD COMPT COMPS KSTD
    (Build_comp COMPT COMPS ct f cfg)
    (Build_msg PAYD mt pl) st t env = v).
Proof.
  intros cd envd ct mt t cfgp v cfg f pl Hpeval Hcfgp st env.
  generalize dependent v.
  dependent inversion t; try discriminate.
  clear H.
  generalize dependent i.
  generalize dependent cfgp.

  unfold eval_hdlr_term.
  fold (eval_hdlr_term PAYD COMPT COMPS KSTD
                       {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
                       {| tag := mt; pay := pl |} st h env).
  unfold peval_hdlr_term.

  generalize (eq_refl (Comp COMPT ct')).

  pattern (eval_hdlr_term PAYD COMPT COMPS KSTD
                       {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
                       {| tag := mt; pay := pl |} st h env).

  dependent inversion h with (fun (hndx : cdesc COMPT)
    (hterm : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt envd hndx) =>

match hndx as _hndx return
  sdenote_cdesc COMPT COMPS _hndx ->
  Prop
with
| Comp ct1 => fun x =>

  (fun s : sdenote_cdesc COMPT COMPS (Comp COMPT ct1) =>
    forall (e : hndx = Comp COMPT ct1)
      (cfgp : shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct)))),
      (forall (i : fin (projT1 (compd_conf (COMPS ct))))
              (v : s[[svec_ith (projT2 (compd_conf (COMPS ct))) i]]),
         shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
         Some v ->
         shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
      forall
      (i : fin (projT1 (comp_conf_desc COMPT COMPS ct1)))
      (v : sdenote_cdesc COMPT COMPS
             (Desc COMPT
                (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i))),

match
     hterm in (Reflex.hdlr_term _ _ _ _ _ _ _ d)
     return
       (d = Comp COMPT ct1 ->
        option
          (sdenote_cdesc COMPT COMPS
             (Desc COMPT
                (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i))))
   with
   | Base d _ => fun _ : d = Comp COMPT ct1 => None
   | CComp =>
       fun EQ : Comp COMPT ct = Comp COMPT ct1 =>
       shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct1)))
         match
           uncomp ct ct1 EQ in (_ = _ct)
           return
             (shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS _ct))))
         with
         | eq_refl => cfgp
         end i
   | CConf ct'0 i0 _ =>
       fun
         _ : Desc COMPT
               (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0) =
             Comp COMPT ct1 => None
   | MVar i0 =>
       fun
         _ : Desc COMPT (svec_ith (projT2 (lkup_tag PAYD mt)) i0) =
             Comp COMPT ct1 => None
   | StVar i0 => fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct1 => None
   end e  = Some v ->

    match
      projT2 s in (_ = _ct)
      return
        (forall _i : fin (projT1 (comp_conf_desc COMPT COMPS _ct)),
         s[[svec_ith (projT2 (comp_conf_desc COMPT COMPS _ct)) _i]])
    with
    | eq_refl =>
        fun
          i0 : fin
                 (projT1
                    (comp_conf_desc COMPT COMPS
                       (comp_type COMPT COMPS (projT1 s)))) =>
        shvec_ith sdenote_desc
          (projT2
             (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS (projT1 s))))
          (comp_conf COMPT COMPS (projT1 s)) i0
    end i = v)
  x

| _ => fun _ => True
end

(eval_hdlr_term PAYD COMPT COMPS KSTD
                {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
                {| tag := mt; pay := pl |} st hterm env)

); try discriminate; simpl.

intros.
apply H.
unfold comp_conf_desc in H1.
rewrite <- H1.
dependent destruction e.
reflexivity.

generalize (shvec_ith (sdenote_cdesc COMPT COMPS) (projT2 KSTD) st i).
rewrite H0.
discriminate.
Qed.

Definition peval_expr {cd envd} ct mt
  (e:expr COMPT (hdlr_term ct mt) envd cd)
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
induction e.
  exact (peval_hdlr_term ct mt t v).

  destruct IHe.
    exact (Some (eval_unop COMPT COMPS _ _ u s)).
    exact None.

  destruct IHe1.
    destruct IHe2.
      exact (Some (eval_binop COMPT COMPS _ _ _ b s s0)).
      exact None.

    exact None.
Defined.

Lemma peval_expr_sound : forall cd envd ct mt
  (e:expr COMPT (hdlr_term ct mt) envd cd) cfgp v cfg f pl,
  peval_expr ct mt e cfgp = Some v ->
  (forall i v,
    shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
    Some v ->
    shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
  (forall st env,
    eval_hdlr_expr PAYD COMPT COMPS KSTD
    (Build_comp COMPT COMPS ct f cfg)
    (Build_msg PAYD mt pl) st env e = v).
Proof.
  intros cd envd ct mt e cfgp v cfg f pl Hpeval Hcfgp st env.

  induction e; simpl in *.
    eapply peval_hdlr_term_sound with (v:=v); eauto.

    destruct (peval_expr ct mt e cfgp); try discriminate.
    inversion Hpeval. rewrite IHe with (v:=s); auto.

    destruct (peval_expr ct mt e1 cfgp); try discriminate;
    destruct (peval_expr ct mt e2 cfgp); try discriminate.
    inversion Hpeval. rewrite IHe1 with (v:=s); auto;
    rewrite IHe2 with (v:=s0); auto.
Qed.

Definition peval_oexpr {cd envd} ct mt
  (oe:option (expr COMPT (hdlr_term ct mt) envd cd))
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
destruct oe.
  exact (peval_expr ct mt e v).
  exact None.
Defined.

Lemma peval_oexpr_sound : forall cd envd ct mt
  (oe:option (expr COMPT (hdlr_term ct mt) envd cd)) cfgp v cfg f pl,
  peval_oexpr ct mt oe cfgp = Some v ->
  (forall i v,
    shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
    Some v ->
    shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
  (forall st env,
    eval_oexpr COMPT COMPS (hdlr_term ct mt)
    (fun d envd env t =>
      eval_hdlr_term PAYD COMPT COMPS KSTD
      (Build_comp COMPT COMPS ct f cfg)
      (Build_msg PAYD mt pl) st t env) env oe = Some v).
Proof.
  intros cd envd ct mt oe cfgp v cfg f pl Hpeval Hcfgp st env.
  destruct oe; try discriminate.
    simpl in *. f_equal.
    pose proof (peval_expr_sound cd envd ct mt e cfgp v cfg f pl Hpeval Hcfgp st env).
    unfold eval_hdlr_expr in *. auto.
Qed.

Fixpoint peval_payload_oexpr ct mt envd n : forall (vd:svec desc n),
  payload_oexpr' COMPT (hdlr_term ct mt) envd n vd ->
  shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) ->
  shvec sdenote_desc_conc_pat vd.
intros vd cfgpe cfgp.
induction n.
  exact tt.

  simpl in *. destruct vd as [vd0 vd']. destruct cfgpe as [oe cfgpe'].
  exact (peval_oexpr ct mt oe cfgp, peval_payload_oexpr ct mt envd n vd' cfgpe' cfgp).
Defined.

Lemma peval_payload_oexpr_sound : forall envd ct mt n vd
  (cfgpe:payload_oexpr' COMPT (hdlr_term ct mt) envd n vd) cfgp cfg f pl,
  (forall i v,
    shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
    Some v ->
    shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
  (forall st env,
    cfgp_incl _
     (eval_hdlr_payload_oexpr PAYD COMPT COMPS KSTD
       (Build_comp COMPT COMPS ct f cfg)
       (Build_msg PAYD mt pl) st envd env (existT _ n vd) cfgpe)
     (peval_payload_oexpr ct mt envd n vd cfgpe cfgp)).
Proof.
  intros envd ct mt n vd cfgpe cfgp cfg f pl Hcfgp st env cfg'.
  apply Bool.leb_implb. unfold Bool.leb.
  match goal with
  |- if ?e then _ else _ =>
    destruct e as [? | ?]_eqn; auto
  end.
  induction n.
    auto.

    destruct vd. destruct cfgpe. destruct cfg'. simpl in *.
    apply andb_prop in Heqb. destruct Heqb.
    destruct (peval_oexpr ct mt o cfgp) as [? | ?]_eqn.
      rewrite peval_oexpr_sound with (v:=s2) (cfgp:=cfgp) in H; auto.
      rewrite H. simpl. apply IHn; auto.

      simpl. apply IHn; auto.
Qed.

Definition is_high_comp_pat ct mt envd cp clblr : bool :=
  let conf := peval_payload_oexpr ct _ _ _ _
    (comp_pat_conf COMPT COMPS (hdlr_term ct mt) envd cp)
    (clblr ct) in
  let cpt := comp_pat_type _ _ _ _ cp in
  (projT1 (bool_of_sumbool (cp_incl_dec (Build_conc_pat COMPT COMPS cpt conf)
    (Build_conc_pat COMPT COMPS cpt (clblr cpt))))).

(*  match get_candidate_pats clblr ct with
  | cfg0::cfgs' =>
    let merged := merge_all_cfgps ct cfgs' cfg0 in
    let conf := get_conc_pat_conf ct _ _ _ _ (comp_pat_conf COMPT COMPS (hdlr_term ct mt) envd cp) merged in
    existsb (fun cp' =>
      (proj1_sig (bool_of_sumbool
      (cp_incl_dec
        (Build_conc_pat COMPT COMPS
          (comp_pat_type _ _ _ _ cp) conf) cp')))) clblr
  | nil => false
  end.*)

Lemma is_high_comp_pat_sound : forall c m envd cp clblr,
  lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
  is_high_comp_pat (comp_type _ _ c) (tag _ m) envd cp clblr = true ->
  forall st env,
    high_comp_pat COMPT COMPTDEC COMPS
      (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD c m st envd env cp)
      (lblr_match_comp COMPT COMPTDEC COMPS clblr).
Proof.
  intros c m envd cp clblr Hmatch Hhigh st env.
  unfold is_high_comp_pat in Hhigh.
  destruct cp as [cpt cpfg]. destruct c as [ct f cfg].
  destruct m as [mt pl]. simpl in *.
  unfold high_comp_pat. intros c' Hmatch'.
  match goal with
  | [ _ : context [ cp_incl_dec ?cp1 ?cp2 ] |- _ ]
    => destruct (cp_incl_dec cp1 cp2); try discriminate
  end. unfold cp_incl in *. clear Hhigh. specialize (c c').
  unfold match_comp, NIExists.match_comp, Reflex.match_comp, match_comp_pf in *.
  simpl in *. unfold hdlr_term, CT, CTAG in *.
  destruct (COMPTDEC (comp_type COMPT COMPS c') cpt); try discriminate.
  destruct e.
  pose proof (peval_payload_oexpr_sound envd ct mt _ _ cpfg (clblr ct) cfg f pl).
Lemma high_comp_cfgp_sound : forall ct f cfg clblr,
  lblr_match_comp COMPT COMPTDEC COMPS clblr
  {| comp_type := ct; comp_fd := f; comp_conf := cfg |} = true ->
  (forall (i : fin (projT1 (comp_conf_desc COMPT COMPS ct)))
         (v : s[[svec_ith (projT2 (comp_conf_desc COMPT COMPS ct)) i]]),
       shvec_ith sdenote_desc_conc_pat (projT2 (comp_conf_desc COMPT COMPS ct))
         (clblr ct) i = Some v ->
       shvec_ith sdenote_desc (projT2 (comp_conf_desc COMPT COMPS ct)) cfg i = v).
Proof.
  intros ct f cfg clblr Hlblr i v Hith.
  unfold lblr_match_comp, NIExists.match_comp,
    Reflex.match_comp, match_comp_pf in Hlblr. simpl in *.
  destruct (COMPTDEC ct ct); try discriminate.
  rewrite UIP_refl with (p:=e) in Hlblr.
Lemma high_comp_cfgp_sound' : forall n vd v (i:fin n) cfg s,
  shvec_match vd sdenote_desc sdenote_desc_conc_pat
    (Reflex.elt_match COMPT COMPS) cfg v = true ->
  shvec_ith sdenote_desc_conc_pat vd v i = Some s ->
  shvec_ith sdenote_desc vd cfg i = s.
Proof.
  intros n vd v i cfg s Hmatch Hith.
  induction n.
    contradiction.

    destruct vd as [vd0 vd']. destruct cfg as [cfg0 cfg'].
    destruct v as [v0 v']. simpl in *.
    apply andb_prop in Hmatch. destruct Hmatch as [Hmatch_elt ?].
    destruct i.
      apply IHn with (v:=v'); auto.

      rewrite Hith in Hmatch_elt. simpl in Hmatch_elt.
      destruct vd0;
        match goal with
        | [ _ : context [ if ?e then _ else _ ] |- _ ]=>
          destruct e; try discriminate; auto
        end.
Qed.
apply high_comp_cfgp_sound' with (v:=

pose (
fun v0 : sigT vdesc' =>
 forall cfg : sdenote_vdesc v0,
 (if if shvec_match (projT2 v0) sdenote_desc sdenote_desc_conc_pat
          (Reflex.elt_match COMPT COMPS) cfg (clblr ct)
     then Some eq_refl
     else None
  then true
  else false) = true ->
 forall (i : fin (projT1 v0)) (v : sdenote_desc (svec_ith (projT2 v0) i)),
 shvec_ith sdenote_desc_conc_pat (projT2 v0) (clblr ct) i = Some v ->
 shvec_ith sdenote_desc (projT2 v0) cfg i = v).
  destruct (comp_conf_desc COMPT COMPS ct).
  cut (shvec_match
                 (projT2
                    (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS c')))
                 sdenote_desc sdenote_desc_conc_pat elt_match
                 (comp_conf COMPT COMPS c')
                 (get_conc_pat_conf ct (tag PAYD m) envd
                    (projT1
                       (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS c')))
                    (projT2
                       (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS c')))
                    cpfg (clblr ct)) = true).
    intro H. unfold elt_match in *. rewrite H in *.
    unfold lblr_match_comp, NIExists.match_comp, Reflex.match_comp, match_comp_pf.
    simpl in *. destruct (COMPTDEC (comp_type COMPT COMPS c') (comp_type COMPT COMPS c')); try intuition.
    rewrite UIP_refl with (p:=e). auto.

    clear c. destruct c' as [ct' ? cfg']. simpl in *.
    destruct (comp_conf_desc COMPT COMPS ct') as [n cfgd].
    induction n.
      auto.

      destruct cfgd. destruct cpfg. destruct cfg'. simpl in *.
      destruct o. simpl in *.
dependent inversion e with (
  fun (c : cdesc COMPT)
   (e : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
          envd c) =>
 (let (elt', rest') :=
      get_conc_pat_conf ct (tag PAYD m) envd (S n)
        (d, s) (Some e, p) (clblr ct) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true
).
Derive Inversion exprinv with (forall d ct mt envd, expr COMPT (hdlr_term ct mt) envd (Desc COMPT d)) Sort Set.
unfold hdlr_term.
Open Scope type_scope.
pose (fun (NB_MSG : nat)
   (PAYD : (fix vec (n : nat) : Type :=
              match n with
              | 0 => unit
              | S n' =>
                  (sigT
                     (fix svec (n0 : nat) : Set :=
                        match n0 with
                        | 0 => unit
                        | S n'0 => desc * svec n'0
                        end) * vec n')%type
              end) NB_MSG) (COMPT : Set) (COMPS : COMPT -> compd)
   (KSTD : sigT
             (fix svec (n : nat) : Set :=
                match n with
                | 0 => unit
                | S n' => cdesc COMPT * svec n'
                end)) (d : desc) (ct : COMPT)
   (mt : (fix fin (n : nat) : Set :=
            match n with
            | 0 => False
            | S n' => option (fin n')
            end) NB_MSG)
   (envd : sigT
             (fix svec (n : nat) : Set :=
                match n with
                | 0 => unit
                | S n' => cdesc COMPT * svec n'
                end)) =>
 (let (elt', rest') :=
      match
        e in (expr _ _ _ c)
        return
          (c = Desc COMPT d ->
           sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
      with
      | Term d0 H =>
          fun H0 : d0 = Desc COMPT d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt envd c ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun
               H1 : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt envd
                      (Desc COMPT d) =>
             (peval_hdlr_term ct mt H1 (clblr ct),
             get_conc_pat_conf ct mt envd n s p (clblr ct))) d0
            (Logic.eq_sym H0) H
      | UnOp d1 d2 H H0 =>
          fun H1 : d2 = Desc COMPT d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             unop COMPT d1 c ->
             expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt) envd
               d1 -> sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : unop COMPT d1 (Desc COMPT d))
               (_ : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt)
                      envd d1) =>
             (None, get_conc_pat_conf ct mt envd n s p (clblr ct))) d2
            (Logic.eq_sym H1) H H0
      | BinOp d1 d2 d3 H H0 H1 =>
          fun H2 : d3 = Desc COMPT d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             binop COMPT d1 d2 c ->
             expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt) envd
               d1 ->
             expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt) envd
               d2 -> sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : binop COMPT d1 d2 (Desc COMPT d))
               (_ : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt)
                      envd d1)
               (_ : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt)
                      envd d2) =>
             (None, get_conc_pat_conf ct mt envd n s p (clblr ct))) d3
            (Logic.eq_sym H2) H H0 H1
      end (eq_refl (Desc COMPT d)) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true).
inversion e using exprinv.
Open Scope type_scope.
pose (fun (NB_MSG : nat)
   (_ : (fix vec (n : nat) : Type :=
           match n with
           | 0 => unit
           | S n' =>
               (sigT
                  (fix svec (n0 : nat) : Set :=
                     match n0 with
                     | 0 => unit
                     | S n'0 => desc * svec n'0
                     end) * vec n')%type
           end) NB_MSG) (COMPT : Set) (_ : COMPT -> compd)
   (_ : sigT
          (fix svec (n : nat) : Set :=
             match n with
             | 0 => unit
             | S n' => cdesc COMPT * svec n'
             end)) (d : desc) ct
   (mt : (fix fin (n : nat) : Set :=
            match n with
            | 0 => False
            | S n' => option (fin n')
            end) NB_MSG)
   (envd : sigT
             (fix svec (n : nat) : Set :=
                match n with
                | 0 => unit
                | S n' => cdesc COMPT * svec n'
                end)) =>
 (let (elt', rest') :=
      match
        e in (expr _ _ _ c)
        return
          (c = Desc _ d ->
           sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
      with
      | Term d0 H =>
          fun H0 : d0 = Desc _ d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             Rehdlr_term ct mt envd c ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun H1 : hdlr_term ct mt envd (Desc COMPT d) =>
             (peval_hdlr_term ct mt H1 (clblr ct),
             get_conc_pat_conf ct mt envd n s p (clblr ct))) d0
            (Logic.eq_sym H0) H
      | UnOp d1 d2 H H0 =>
          fun H1 : d2 = Desc COMPT d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             unop COMPT d1 c ->
             expr COMPT (hdlr_term ct mt) envd d1 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : unop COMPT d1 (Desc COMPT d))
               (_ : expr COMPT (hdlr_term ct mt) envd d1) =>
             (None, get_conc_pat_conf ct mt envd n s p (clblr ct))) d2
            (Logic.eq_sym H1) H H0
      | BinOp d1 d2 d3 H H0 H1 =>
          fun H2 : d3 = Desc COMPT d =>
          eq_rec (Desc COMPT d)
            (fun c : cdesc COMPT =>
             binop COMPT d1 d2 c ->
             expr COMPT (hdlr_term ct mt) envd d1 ->
             expr COMPT (hdlr_term ct mt) envd d2 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : binop COMPT d1 d2 (Desc COMPT d))
               (_ : expr COMPT (hdlr_term ct mt) envd d1)
               (_ : expr COMPT (hdlr_term ct mt) envd d2) =>
             (None, get_conc_pat_conf ct mt envd n s p (clblr ct))) d3
            (Logic.eq_sym H2) H H0 H1
      end (eq_refl (Desc COMPT d)) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true).
inversion e using exprinv.
dependent inversion e with (
  fun (cd:cdesc COMPT)
  (e:expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
      envd cd) =>
(let (elt', rest') :=
        match
          e in (expr _ _ _ c)
          return
            (c = Desc COMPT d ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
        with
        | Term d0 H =>
            fun H0 : d0 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               hdlr_term ct (tag PAYD m) envd c ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun H1 : hdlr_term ct (tag PAYD m) envd (Desc COMPT d) =>
               (peval_hdlr_term ct (tag PAYD m) H1 (clblr ct),
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d0
              (Logic.eq_sym H0) H
        | UnOp d1 d2 H H0 =>
            fun H1 : d2 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               unop COMPT d1 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : unop COMPT d1 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d2
              (Logic.eq_sym H1) H H0
        | BinOp d1 d2 d3 H H0 H1 =>
            fun H2 : d3 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               binop COMPT d1 d2 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : binop COMPT d1 d2 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d3
              (Logic.eq_sym H2) H H0 H1
        end (eq_refl cd) in
    (elt_match d s0 elt' &&
     shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
   true).

    shvec_match (n:=S n) (projT2 (existT vdesc' (S n) (d, s))) sdenote_desc
     sdenote_desc_conc_pat elt_match (s0, s1)
     (get_conc_pat_conf ct (tag PAYD m) envd
        (projT1 (existT vdesc' (S n) (d, s)))
        (projT2 (existT vdesc' (S n) (d, s))) (Some e, p)
        (clblr ct)) = true).


        auto.
      generalize s0. rewrite H.
dependent inversion e with (
  fun (cd:cdesc COMPT)
(e:expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
        envd cd) =>
forall s2 : sdenote_desc d,
   (let (elt', rest') :=
        match
          e in (expr _ _ _ c)
          return
            (c = cd ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
        with
        | Term d0 H =>
            fun H0 : _ =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               hdlr_term ct (tag PAYD m) envd c ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun H1 : hdlr_term ct (tag PAYD m) envd (Desc COMPT d) =>
               (peval_hdlr_term ct (tag PAYD m) H1 (clblr ct),
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d0
              (Logic.eq_sym H0) H
        | UnOp d1 d2 H H0 =>
            fun H1 : d2 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               unop COMPT d1 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : unop COMPT d1 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d2
              (Logic.eq_sym H1) H H0
        | BinOp d1 d2 d3 H H0 H1 =>
            fun H2 : d3 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               binop COMPT d1 d2 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : binop COMPT d1 d2 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d3
              (Logic.eq_sym H2) H H0 H1
        end (eq_refl _) in
    (elt_match d s2 elt' &&
     shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
   true
).

destruct e.
refine (
  let elt' :=
    fst (match
    e in (expr _ _ _ c)
    return
    (c = Desc COMPT d ->
      sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
    with
    | Term _ _ => _
    | _ => fun _ => (None, _)
    end (Logic.eq_refl _)) in
  _). admit. admit. admit.
  (elt_match d s0 elt' &&
    shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool =
  true).

dependent inversion e.
        dependent inversion e with (
fun (d:desc)
(e:expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
        envd (Desc COMPT d))
=>
(let (elt', rest') :=
        match
          e in (expr _ _ _ c)
          return
            (c = Desc COMPT d ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
        with
        | Term d0 H =>
            fun H0 : d0 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               hdlr_term ct (tag PAYD m) envd c ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun H1 : hdlr_term ct (tag PAYD m) envd (Desc COMPT d) =>
               match
                 H1 in (Reflex.hdlr_term _ _ _ _ _ _ _ c)
                 return
                   (c = Desc COMPT d ->
                    sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
               with
               | Base d1 H2 =>
                   fun H3 : d1 = Desc COMPT d =>
                   eq_rec (Desc COMPT d)
                     (fun c : cdesc COMPT =>
                      Reflex.base_term COMPT envd c ->
                      sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                     (fun _ : Reflex.base_term COMPT envd (Desc COMPT d) =>
                      (None,
                      get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
                     d1 (Logic.eq_sym H3) H2
               | CComp =>
                   fun H2 : Comp COMPT ct = Desc COMPT d =>
                   False_rec
                     (sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                     (eq_ind (Comp COMPT ct)
                        (fun e0 : cdesc COMPT =>
                         match e0 with
                         | Desc _ => False
                         | Comp _ => True
                         end) I (Desc COMPT d) H2)
               | CConf ct'0 i H2 =>
                   fun
                     H3 : Desc COMPT
                            (svec_ith
                               (projT2 (comp_conf_desc COMPT COMPS ct'0)) i) =
                          Desc COMPT d =>
                   eq_rec
                     (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'0)) i)
                     (fun d1 : desc =>
                      Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                        (tag PAYD m) envd (Comp COMPT ct'0) ->
                      sdenote_desc_conc_pat d1 *
                      shvec sdenote_desc_conc_pat s)
                     (fun
                        H4 : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                               (tag PAYD m) envd (Comp COMPT ct'0) =>
                      match
                        H4 in (Reflex.hdlr_term _ _ _ _ _ _ _ c)
                        return
                          (c = Comp COMPT ct'0 ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct'0)) i) *
                           shvec sdenote_desc_conc_pat s)
                      with
                      | Base d1 H5 =>
                          fun H6 : d1 = Comp COMPT ct'0 =>
                          eq_rec (Comp COMPT ct'0)
                            (fun c : cdesc COMPT =>
                             Reflex.base_term COMPT envd c ->
                             sdenote_desc_conc_pat
                               (svec_ith
                                  (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                  i) * shvec sdenote_desc_conc_pat s)
                            (fun
                               _ : Reflex.base_term COMPT envd
                                     (Comp COMPT ct'0) =>
                             (None,
                             get_conc_pat_conf ct (tag PAYD m) envd n s p
                               (clblr ct))) d1 (Logic.eq_sym H6) H5
                      | CComp =>
                          fun H5 : Comp COMPT ct = Comp COMPT ct'0 =>
                          eq_rec ct
                            (fun ct'1 : COMPT =>
                             forall
                               i0 : fin
                                      (projT1
                                         (comp_conf_desc COMPT COMPS ct'1)),
                             Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                               (tag PAYD m) envd (Comp COMPT ct'1) ->
                             svec_ith
                               (projT2 (comp_conf_desc COMPT COMPS ct'1)) i0 =
                             d ->
                             sdenote_desc_conc_pat
                               (svec_ith
                                  (projT2 (comp_conf_desc COMPT COMPS ct'1))
                                  i0) * shvec sdenote_desc_conc_pat s)
                            (fun
                               (i0 : fin
                                       (projT1
                                          (comp_conf_desc COMPT COMPS ct)))
                               (_ : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                                      (tag PAYD m) envd
                                      (Comp COMPT ct))
                               (_ : svec_ith
                                      (projT2 (comp_conf_desc COMPT COMPS ct))
                                      i0 = d) =>
                             (shvec_ith sdenote_desc_conc_pat
                                (projT2 (compd_conf (COMPS ct)))
                                (clblr ct) i0,
                             get_conc_pat_conf ct (tag PAYD m) envd n s p
                               (clblr ct))) ct'0
                            (f_equal
                               (fun e0 : cdesc COMPT =>
                                match e0 with
                                | Desc _ => ct
                                | Comp c => c
                                end) H5) i H4
                            (f_equal
                               (fun e0 : cdesc COMPT =>
                                match e0 with
                                | Desc d1 => d1
                                | Comp _ =>
                                    (fix svec_ith (n0 : nat) :
                                       svec desc n0 -> fin n0 -> desc :=
                                       match
                                         n0 as n1
                                         return
                                           (svec desc n1 -> fin n1 -> desc)
                                       with
                                       | 0 =>
                                           fun (_ : unit) (idx : False) =>
                                           match idx return desc with
                                           end
                                       | S n' =>
                                           fun (v : desc * svec desc n')
                                             (idx : option (fin n')) =>
                                           match idx with
                                           | Some idx' =>
                                               svec_ith n' (snd v) idx'
                                           | None => fst v
                                           end
                                       end)
                                      (projT1
                                         (comp_conf_desc COMPT COMPS ct'0))
                                      (projT2
                                         (comp_conf_desc COMPT COMPS ct'0)) i
                                end) H3)
                      | CConf ct'1 i0 H5 =>
                          fun
                            H6 : Desc COMPT
                                   (svec_ith
                                      (projT2
                                         (comp_conf_desc COMPT COMPS ct'1))
                                      i0) = Comp COMPT ct'0 =>
                          False_rec
                            (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                               (tag PAYD m) envd (Comp COMPT ct'1) ->
                             sdenote_desc_conc_pat
                               (svec_ith
                                  (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                  i) * shvec sdenote_desc_conc_pat s)
                            (eq_ind
                               (Desc COMPT
                                  (svec_ith
                                     (projT2
                                        (comp_conf_desc COMPT COMPS ct'1)) i0))
                               (fun e0 : cdesc COMPT =>
                                match e0 with
                                | Desc _ => True
                                | Comp _ => False
                                end) I (Comp COMPT ct'0) H6) H5
                      | MVar i0 =>
                          fun
                            H5 : Desc COMPT
                                   (svec_ith
                                      (projT2 (lkup_tag PAYD (tag PAYD m)))
                                      i0) = Comp COMPT ct'0 =>
                          False_rec
                            (sdenote_desc_conc_pat
                               (svec_ith
                                  (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                  i) * shvec sdenote_desc_conc_pat s)
                            (eq_ind
                               (Desc COMPT
                                  (svec_ith
                                     (projT2 (lkup_tag PAYD (tag PAYD m))) i0))
                               (fun e0 : cdesc COMPT =>
                                match e0 with
                                | Desc _ => True
                                | Comp _ => False
                                end) I (Comp COMPT ct'0) H5)
                      | StVar i0 =>
                          fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct'0 =>
                          (None,
                          get_conc_pat_conf ct (tag PAYD m) envd n s p
                            (clblr ct))
                      end (eq_refl (Comp COMPT ct'0))) d
                     (f_equal
                        (fun e0 : cdesc COMPT =>
                         match e0 with
                         | Desc d1 => d1
                         | Comp _ =>
                             (fix svec_ith (n0 : nat) :
                                svec desc n0 -> fin n0 -> desc :=
                                match
                                  n0 as n1
                                  return (svec desc n1 -> fin n1 -> desc)
                                with
                                | 0 =>
                                    fun (_ : unit) (idx : False) =>
                                    match idx return desc with
                                    end
                                | S n' =>
                                    fun (v : desc * svec desc n')
                                      (idx : option (fin n')) =>
                                    match idx with
                                    | Some idx' => svec_ith n' (snd v) idx'
                                    | None => fst v
                                    end
                                end)
                               (projT1 (comp_conf_desc COMPT COMPS ct'0))
                               (projT2 (comp_conf_desc COMPT COMPS ct'0)) i
                         end) H3) H2
               | MVar i =>
                   fun
                     H2 : Desc COMPT
                            (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i) =
                          Desc COMPT d =>
                   eq_rec (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i)
                     (fun d1 : desc =>
                      (sdenote_desc_conc_pat d1 *
                       shvec sdenote_desc_conc_pat s)%type)
                     (None,
                     get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))
                     d
                     (f_equal
                        (fun e0 : cdesc COMPT =>
                         match e0 with
                         | Desc d1 => d1
                         | Comp _ =>
                             (fix svec_ith (n0 : nat) :
                                svec desc n0 -> fin n0 -> desc :=
                                match
                                  n0 as n1
                                  return (svec desc n1 -> fin n1 -> desc)
                                with
                                | 0 =>
                                    fun (_ : unit) (idx : False) =>
                                    match idx return desc with
                                    end
                                | S n' =>
                                    fun (v : desc * svec desc n')
                                      (idx : option (fin n')) =>
                                    match idx with
                                    | Some idx' => svec_ith n' (snd v) idx'
                                    | None => fst v
                                    end
                                end) (projT1 (lkup_tag PAYD (tag PAYD m)))
                               (projT2 (lkup_tag PAYD (tag PAYD m))) i
                         end) H2)
               | StVar i =>
                   fun _ : svec_ith (projT2 KSTD) i = Desc COMPT d =>
                   (None,
                   get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))
               end (eq_refl (Desc COMPT d))) d0 (Logic.eq_sym H0) H
        | UnOp d1 d2 H H0 =>
            fun H1 : d2 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               unop COMPT d1 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : unop COMPT d1 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d2
              (Logic.eq_sym H1) H H0
        | BinOp d1 d2 d3 H H0 H1 =>
            fun H2 : d3 = Desc COMPT d =>
            eq_rec (Desc COMPT d)
              (fun c : cdesc COMPT =>
               binop COMPT d1 d2 c ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
               expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
               sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
              (fun (_ : binop COMPT d1 d2 (Desc COMPT d))
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
                 (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
               (None,
               get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))) d3
              (Logic.eq_sym H2) H H0 H1
        end (eq_refl (Desc COMPT d)) in
    (elt_match d s0 elt' &&
     shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
   true).

Variable ct : COMPT.
Variable  comp_fd : fd.
Variable  cfg : sdenote_vdesc (comp_conf_desc COMPT COMPS ct).
Variable  m : msg PAYD.
Variable  envd : vcdesc COMPT.
Variable  ct' : COMPT.
Variable  comp_fd0 : fd.
Variable  n : nat.
Variable  d : desc.
Variable  s : (fix svec (n : nat) : Set :=
         match n with
         | 0 => unit
         | S n' => (desc * svec n')%type
         end) n.
Variable  s0 : sdenote_desc d.
Variable  s1 : (fix shvec (n : nat) : svec desc n -> Set :=
          match n as n0 return (svec desc n0 -> Set) with
          | 0 => fun _ : unit => unit
          | S n' =>
              fun v : desc * svec desc n' =>
              let (t, v') := v in (sdenote_desc t * shvec n' v')%type
          end) n s.
Variable  e : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
        envd (Desc COMPT d).
Variable  p : (fix payload_oexpr' (envd : vcdesc COMPT) (n : nat)
                          (pd : vdesc' n) {struct n} :
       Type :=
         match n as _n return (vdesc' _n -> Type) with
         | 0 => fun _ : unit => unit
         | S n' =>
             fun pd0 : desc * vdesc' n' =>
             let (d, pd') := pd0 in
             (option
                (expr COMPT
                   (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
                   envd (Desc COMPT d)) * payload_oexpr' envd n' pd')%type
         end pd) envd n s.
Variable  clblr : forall ct : COMPT,
          shvec sdenote_desc_conc_pat
            (projT2 (comp_conf_desc COMPT COMPS ct)).
Variable env : sdenote_vcdesc COMPT COMPS envd.
Variable st : sdenote_vcdesc COMPT COMPS KSTD.
Definition stupid :=
fun (c : cdesc COMPT)
   (e : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
          envd c) =>
 (let (elt', rest') :=
      match
        e in (expr _ _ _ c0)
        return
          (c0 = c -> sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
      with
      | Term d H =>
          fun H0 : d = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             hdlr_term ct (tag PAYD m) envd c0 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun H1 : hdlr_term ct (tag PAYD m) envd c =>
             match
               H1 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
               return
                 (c0 = c ->
                  sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
             with
             | Base d0 H2 =>
                 fun H3 : d0 = c =>
                 eq_rec c
                   (fun c0 : cdesc COMPT =>
                    Reflex.base_term COMPT envd c0 ->
                    sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (fun _ : Reflex.base_term COMPT envd c =>
                    (None,
                    get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
                   d0 (Logic.eq_sym H3) H2
             | CComp =>
                 fun H2 : Comp COMPT ct = c =>
                 False_rec
                   (sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (eq_ind (Comp COMPT ct)
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc _ => False
                       | Comp _ => True
                       end) I c H2)
             | CConf ct' i H2 =>
                 fun
                   H3 : Desc COMPT
                          (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'))
                             i) = c =>
                 eq_rec
                   (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct')) i)
                   (fun d0 : desc =>
                    Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                      (tag PAYD m) envd (Comp COMPT ct') ->
                    sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)
                   (fun
                      H4 : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct') =>
                    match
                      H4 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
                      return
                        (c0 = Comp COMPT ct' ->
                         sdenote_desc_conc_pat
                           (svec_ith
                              (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                         shvec sdenote_desc_conc_pat s)
                    with
                    | Base d0 H5 =>
                        fun H6 : d0 = Comp COMPT ct' =>
                        eq_rec (Comp COMPT ct')
                          (fun c0 : cdesc COMPT =>
                           Reflex.base_term COMPT envd c0 ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             _ : Reflex.base_term COMPT envd (Comp COMPT ct') =>
                           (None,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) d0 (Logic.eq_sym H6) H5
                    | CComp =>
                        fun H5 : Comp COMPT ct = Comp COMPT ct' =>
                        eq_rec ct
                          (fun ct'0 : COMPT =>
                           forall
                             i0 : fin
                                    (projT1 (comp_conf_desc COMPT COMPS ct'0)),
                           Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           svec_ith
                             (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0 =
                           d ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             (i0 : fin
                                     (projT1 (comp_conf_desc COMPT COMPS ct)))
                             (_ : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                                    (tag PAYD m) envd
                                    (Comp COMPT ct))
                             (_ : svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct))
                                    i0 = d) =>
                           (shvec_ith sdenote_desc_conc_pat
                              (projT2 (compd_conf (COMPS ct)))
                              (clblr ct) i0,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) ct'
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => ct
                              | Comp c0 => c0
                              end) H5) i H4
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc d0 => d0
                              | Comp _ =>
                                  (fix svec_ith (n : nat) :
                                     svec desc n -> fin n -> desc :=
                                     match
                                       n as n0
                                       return
                                         (svec desc n0 -> fin n0 -> desc)
                                     with
                                     | 0 =>
                                         fun (_ : unit) (idx : False) =>
                                         match idx return desc with
                                         end
                                     | S n' =>
                                         fun (v : desc * svec desc n')
                                           (idx : option (fin n')) =>
                                         match idx with
                                         | Some idx' =>
                                             svec_ith n' (snd v) idx'
                                         | None => fst v
                                         end
                                     end)
                                    (projT1 (comp_conf_desc COMPT COMPS ct'))
                                    (projT2 (comp_conf_desc COMPT COMPS ct'))
                                    i
                              end) H3)
                    | CConf ct'0 i0 H5 =>
                        fun
                          H6 : Desc COMPT
                                 (svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                    i0) = Comp COMPT ct' =>
                        False_rec
                          (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                   i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H6) H5
                    | MVar i0 =>
                        fun
                          H5 : Desc COMPT
                                 (svec_ith
                                    (projT2 (lkup_tag PAYD (tag PAYD m))) i0) =
                               Comp COMPT ct' =>
                        False_rec
                          (sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (lkup_tag PAYD (tag PAYD m))) i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H5)
                    | StVar i0 =>
                        fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct' =>
                        (None,
                        get_conc_pat_conf ct (tag PAYD m) envd n s p
                          (clblr ct))
                    end (eq_refl (Comp COMPT ct'))) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (comp_conf_desc COMPT COMPS ct'))
                             (projT2 (comp_conf_desc COMPT COMPS ct')) i
                       end) H3) H2
             | MVar i =>
                 fun
                   H2 : Desc COMPT
                          (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i) =
                        c =>
                 eq_rec (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i)
                   (fun d0 : desc =>
                    (sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)%type)
                   (None,
                   get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (lkup_tag PAYD (tag PAYD m)))
                             (projT2 (lkup_tag PAYD (tag PAYD m))) i
                       end) H2)
             | StVar i =>
                 fun _ : svec_ith (projT2 KSTD) i = c =>
                 (None,
                 get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))
             end (eq_refl c)) d (Logic.eq_sym H0) H
      | UnOp d1 d2 H H0 =>
          fun H1 : d2 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             unop COMPT d1 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : unop COMPT d1 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d2 (Logic.eq_sym H1) H H0
      | BinOp d1 d2 d3 H H0 H1 =>
          fun H2 : d3 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             binop COMPT d1 d2 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : binop COMPT d1 d2 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d3 (Logic.eq_sym H2) H H0 H1
      end (eq_refl c) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true.
Definition blah :=
fun (c : cdesc COMPT)
   (e : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
          envd c) =>
 (if if (elt_match d s0
           (eval_oexpr COMPT COMPS
              (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (CTAG PAYD m))
              (fun (d : cdesc COMPT) (envd : vcdesc COMPT)
                 (e0 : sdenote_vcdesc COMPT COMPS envd)
                 (t : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                        (CTAG PAYD m) envd d) =>
               eval_hdlr_term PAYD COMPT COMPS KSTD
                 {| comp_type := ct; comp_fd := comp_fd; comp_conf := cfg |}
                 m st t e0) env (Some e)) &&
         shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1
           (eval_payload_oexpr' COMPT COMPS
              (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (CTAG PAYD m))
              (fun (d : cdesc COMPT) (envd : vcdesc COMPT)
                 (e0 : sdenote_vcdesc COMPT COMPS envd)
                 (t : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                        (CTAG PAYD m) envd d) =>
               eval_hdlr_term PAYD COMPT COMPS KSTD
                 {| comp_type := ct; comp_fd := comp_fd; comp_conf := cfg |}
                 m st t e0) envd env n s p))%bool
     then Some (eq_refl ct')
     else None
  then true
  else false) = true ->
 (let (elt', rest') :=
      match
        e in (expr _ _ _ c0)
        return
          (c0 = c -> sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
      with
      | Term d H =>
          fun H0 : d = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             hdlr_term ct (tag PAYD m) envd c0 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun H1 : hdlr_term ct (tag PAYD m) envd c =>
             match
               H1 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
               return
                 (c0 = c ->
                  sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
             with
             | Base d0 H2 =>
                 fun H3 : d0 = c =>
                 eq_rec c
                   (fun c0 : cdesc COMPT =>
                    Reflex.base_term COMPT envd c0 ->
                    sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (fun _ : Reflex.base_term COMPT envd c =>
                    (None,
                    get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
                   d0 (Logic.eq_sym H3) H2
             | CComp =>
                 fun H2 : Comp COMPT ct = c =>
                 False_rec
                   (sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (eq_ind (Comp COMPT ct)
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc _ => False
                       | Comp _ => True
                       end) I c H2)
             | CConf ct' i H2 =>
                 fun
                   H3 : Desc COMPT
                          (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'))
                             i) = c =>
                 eq_rec
                   (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct')) i)
                   (fun d0 : desc =>
                    Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                      (tag PAYD m) envd (Comp COMPT ct') ->
                    sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)
                   (fun
                      H4 : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct') =>
                    match
                      H4 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
                      return
                        (c0 = Comp COMPT ct' ->
                         sdenote_desc_conc_pat
                           (svec_ith
                              (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                         shvec sdenote_desc_conc_pat s)
                    with
                    | Base d0 H5 =>
                        fun H6 : d0 = Comp COMPT ct' =>
                        eq_rec (Comp COMPT ct')
                          (fun c0 : cdesc COMPT =>
                           Reflex.base_term COMPT envd c0 ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             _ : Reflex.base_term COMPT envd (Comp COMPT ct') =>
                           (None,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) d0 (Logic.eq_sym H6) H5
                    | CComp =>
                        fun H5 : Comp COMPT ct = Comp COMPT ct' =>
                        eq_rec ct
                          (fun ct'0 : COMPT =>
                           forall
                             i0 : fin
                                    (projT1 (comp_conf_desc COMPT COMPS ct'0)),
                           Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           svec_ith
                             (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0 =
                           d ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             (i0 : fin
                                     (projT1 (comp_conf_desc COMPT COMPS ct)))
                             (_ : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                                    (tag PAYD m) envd
                                    (Comp COMPT ct))
                             (_ : svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct))
                                    i0 = d) =>
                           (shvec_ith sdenote_desc_conc_pat
                              (projT2 (compd_conf (COMPS ct)))
                              (clblr ct) i0,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) ct'
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => ct
                              | Comp c0 => c0
                              end) H5) i H4
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc d0 => d0
                              | Comp _ =>
                                  (fix svec_ith (n : nat) :
                                     svec desc n -> fin n -> desc :=
                                     match
                                       n as n0
                                       return
                                         (svec desc n0 -> fin n0 -> desc)
                                     with
                                     | 0 =>
                                         fun (_ : unit) (idx : False) =>
                                         match idx return desc with
                                         end
                                     | S n' =>
                                         fun (v : desc * svec desc n')
                                           (idx : option (fin n')) =>
                                         match idx with
                                         | Some idx' =>
                                             svec_ith n' (snd v) idx'
                                         | None => fst v
                                         end
                                     end)
                                    (projT1 (comp_conf_desc COMPT COMPS ct'))
                                    (projT2 (comp_conf_desc COMPT COMPS ct'))
                                    i
                              end) H3)
                    | CConf ct'0 i0 H5 =>
                        fun
                          H6 : Desc COMPT
                                 (svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                    i0) = Comp COMPT ct' =>
                        False_rec
                          (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                   i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H6) H5
                    | MVar i0 =>
                        fun
                          H5 : Desc COMPT
                                 (svec_ith
                                    (projT2 (lkup_tag PAYD (tag PAYD m))) i0) =
                               Comp COMPT ct' =>
                        False_rec
                          (sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (lkup_tag PAYD (tag PAYD m))) i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H5)
                    | StVar i0 =>
                        fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct' =>
                        (None,
                        get_conc_pat_conf ct (tag PAYD m) envd n s p
                          (clblr ct))
                    end (eq_refl (Comp COMPT ct'))) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (comp_conf_desc COMPT COMPS ct'))
                             (projT2 (comp_conf_desc COMPT COMPS ct')) i
                       end) H3) H2
             | MVar i =>
                 fun
                   H2 : Desc COMPT
                          (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i) =
                        c =>
                 eq_rec (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i)
                   (fun d0 : desc =>
                    (sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)%type)
                   (None,
                   get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (lkup_tag PAYD (tag PAYD m)))
                             (projT2 (lkup_tag PAYD (tag PAYD m))) i
                       end) H2)
             | StVar i =>
                 fun _ : svec_ith (projT2 KSTD) i = c =>
                 (None,
                 get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))
             end (eq_refl c)) d (Logic.eq_sym H0) H
      | UnOp d1 d2 H H0 =>
          fun H1 : d2 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             unop COMPT d1 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : unop COMPT d1 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d2 (Logic.eq_sym H1) H H0
      | BinOp d1 d2 d3 H H0 H1 =>
          fun H2 : d3 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             binop COMPT d1 d2 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : binop COMPT d1 d2 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d3 (Logic.eq_sym H2) H H0 H1
      end (eq_refl c) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true.

Definition blah :=
  fun (c : cdesc COMPT)
   (e : expr COMPT (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct (tag PAYD m))
          envd c) =>
 (let (elt', rest') :=
      match
        e in (expr _ _ _ c0)
        return
          (c0 = c -> sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
      with
      | Term d H =>
          fun H0 : d = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             hdlr_term ct (tag PAYD m) envd c0 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun H1 : hdlr_term ct (tag PAYD m) envd c =>
             match
               H1 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
               return
                 (c0 = c ->
                  sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
             with
             | Base d0 H2 =>
                 fun H3 : d0 = c =>
                 eq_rec c
                   (fun c0 : cdesc COMPT =>
                    Reflex.base_term COMPT envd c0 ->
                    sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (fun _ : Reflex.base_term COMPT envd c =>
                    (None,
                    get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
                   d0 (Logic.eq_sym H3) H2
             | CComp =>
                 fun H2 : Comp COMPT ct = c =>
                 False_rec
                   (sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
                   (eq_ind (Comp COMPT ct)
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc _ => False
                       | Comp _ => True
                       end) I c H2)
             | CConf ct' i H2 =>
                 fun
                   H3 : Desc COMPT
                          (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'))
                             i) = c =>
                 eq_rec
                   (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct')) i)
                   (fun d0 : desc =>
                    Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                      (tag PAYD m) envd (Comp COMPT ct') ->
                    sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)
                   (fun
                      H4 : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct') =>
                    match
                      H4 in (Reflex.hdlr_term _ _ _ _ _ _ _ c0)
                      return
                        (c0 = Comp COMPT ct' ->
                         sdenote_desc_conc_pat
                           (svec_ith
                              (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                         shvec sdenote_desc_conc_pat s)
                    with
                    | Base d0 H5 =>
                        fun H6 : d0 = Comp COMPT ct' =>
                        eq_rec (Comp COMPT ct')
                          (fun c0 : cdesc COMPT =>
                           Reflex.base_term COMPT envd c0 ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             _ : Reflex.base_term COMPT envd (Comp COMPT ct') =>
                           (None,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) d0 (Logic.eq_sym H6) H5
                    | CComp =>
                        fun H5 : Comp COMPT ct = Comp COMPT ct' =>
                        eq_rec ct
                          (fun ct'0 : COMPT =>
                           forall
                             i0 : fin
                                    (projT1 (comp_conf_desc COMPT COMPS ct'0)),
                           Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           svec_ith
                             (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0 =
                           d ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0) *
                           shvec sdenote_desc_conc_pat s)
                          (fun
                             (i0 : fin
                                     (projT1 (comp_conf_desc COMPT COMPS ct)))
                             (_ : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                                    (tag PAYD m) envd
                                    (Comp COMPT ct))
                             (_ : svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct))
                                    i0 = d) =>
                           (shvec_ith sdenote_desc_conc_pat
                              (projT2 (compd_conf (COMPS ct)))
                              (clblr ct) i0,
                           get_conc_pat_conf ct (tag PAYD m) envd n s p
                             (clblr ct))) ct'
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => ct
                              | Comp c0 => c0
                              end) H5) i H4
                          (f_equal
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc d0 => d0
                              | Comp _ =>
                                  (fix svec_ith (n : nat) :
                                     svec desc n -> fin n -> desc :=
                                     match
                                       n as n0
                                       return
                                         (svec desc n0 -> fin n0 -> desc)
                                     with
                                     | 0 =>
                                         fun (_ : unit) (idx : False) =>
                                         match idx return desc with
                                         end
                                     | S n' =>
                                         fun (v : desc * svec desc n')
                                           (idx : option (fin n')) =>
                                         match idx with
                                         | Some idx' =>
                                             svec_ith n' (snd v) idx'
                                         | None => fst v
                                         end
                                     end)
                                    (projT1 (comp_conf_desc COMPT COMPS ct'))
                                    (projT2 (comp_conf_desc COMPT COMPS ct'))
                                    i
                              end) H3)
                    | CConf ct'0 i0 H5 =>
                        fun
                          H6 : Desc COMPT
                                 (svec_ith
                                    (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                    i0) = Comp COMPT ct' =>
                        False_rec
                          (Reflex.hdlr_term PAYD COMPT COMPS KSTD ct
                             (tag PAYD m) envd (Comp COMPT ct'0) ->
                           sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (comp_conf_desc COMPT COMPS ct'0))
                                   i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H6) H5
                    | MVar i0 =>
                        fun
                          H5 : Desc COMPT
                                 (svec_ith
                                    (projT2 (lkup_tag PAYD (tag PAYD m))) i0) =
                               Comp COMPT ct' =>
                        False_rec
                          (sdenote_desc_conc_pat
                             (svec_ith
                                (projT2 (comp_conf_desc COMPT COMPS ct')) i) *
                           shvec sdenote_desc_conc_pat s)
                          (eq_ind
                             (Desc COMPT
                                (svec_ith
                                   (projT2 (lkup_tag PAYD (tag PAYD m))) i0))
                             (fun e0 : cdesc COMPT =>
                              match e0 with
                              | Desc _ => True
                              | Comp _ => False
                              end) I (Comp COMPT ct') H5)
                    | StVar i0 =>
                        fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct' =>
                        (None,
                        get_conc_pat_conf ct (tag PAYD m) envd n s p
                          (clblr ct))
                    end (eq_refl (Comp COMPT ct'))) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (comp_conf_desc COMPT COMPS ct'))
                             (projT2 (comp_conf_desc COMPT COMPS ct')) i
                       end) H3) H2
             | MVar i =>
                 fun
                   H2 : Desc COMPT
                          (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i) =
                        c =>
                 eq_rec (svec_ith (projT2 (lkup_tag PAYD (tag PAYD m))) i)
                   (fun d0 : desc =>
                    (sdenote_desc_conc_pat d0 * shvec sdenote_desc_conc_pat s)%type)
                   (None,
                   get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)) d
                   (f_equal
                      (fun e0 : cdesc COMPT =>
                       match e0 with
                       | Desc d0 => d0
                       | Comp _ =>
                           (fix svec_ith (n : nat) :
                              svec desc n -> fin n -> desc :=
                              match
                                n as n0
                                return (svec desc n0 -> fin n0 -> desc)
                              with
                              | 0 =>
                                  fun (_ : unit) (idx : False) =>
                                  match idx return desc with
                                  end
                              | S n' =>
                                  fun (v : desc * svec desc n')
                                    (idx : option (fin n')) =>
                                  match idx with
                                  | Some idx' => svec_ith n' (snd v) idx'
                                  | None => fst v
                                  end
                              end) (projT1 (lkup_tag PAYD (tag PAYD m)))
                             (projT2 (lkup_tag PAYD (tag PAYD m))) i
                       end) H2)
             | StVar i =>
                 fun _ : svec_ith (projT2 KSTD) i = c =>
                 (None,
                 get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct))
             end (eq_refl c)) d (Logic.eq_sym H0) H
      | UnOp d1 d2 H H0 =>
          fun H1 : d2 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             unop COMPT d1 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : unop COMPT d1 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d2 (Logic.eq_sym H1) H H0
      | BinOp d1 d2 d3 H H0 H1 =>
          fun H2 : d3 = c =>
          eq_rec c
            (fun c0 : cdesc COMPT =>
             binop COMPT d1 d2 c0 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d1 ->
             expr COMPT (hdlr_term ct (tag PAYD m)) envd d2 ->
             sdenote_desc_conc_pat d * shvec sdenote_desc_conc_pat s)
            (fun (_ : binop COMPT d1 d2 c)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d1)
               (_ : expr COMPT (hdlr_term ct (tag PAYD m)) envd d2) =>
             (None, get_conc_pat_conf ct (tag PAYD m) envd n s p (clblr ct)))
            d3 (Logic.eq_sym H2) H H0 H1
      end (eq_refl c) in
  (elt_match d s0 elt' &&
   shvec_match s sdenote_desc sdenote_desc_conc_pat elt_match s1 rest')%bool) =
 true.

        dependent inversion e.
        destruct d. simpl in *. destruct e.

    destruct (COMPTDEC comp_type (conc_pat_type COMPT COMPS x)); try discriminate.
      destruct x. simpl in *. destruct e. unfold lblr_match_comp.
      apply existsb_exists. exists ({| conc_pat_type := comp_type; conc_pat_conf := conc_pat_conf |}).
      split; auto. unfold NIExists.match_comp, Reflex.match_comp, match_comp_pf. simpl.
      destruct (COMPTDEC comp_type comp_type); try intuition. rewrite UIP_refl with (p:=e). auto.
  destruct (comp_conf_desc COMPT COMPS cpt).
  destruct (comp_conf_desc COMPT COMPS
                                           (comp_pat_type COMPT COMPS
                                              (hdlr_term
                                                 (comp_type COMPT COMPS c)
                                                 (tag PAYD m)) envd cp)).
  destruct (get_candidate_pats clblr (comp_type COMPT COMPS c)) as [? | ?]_eqn.
    discriminate.

    apply existsb_exists in Hhigh. destruct Hhigh. destruct H.
    match goal with
    | [ _ : context [ cp_incl_dec ?cp1 ?cp2 ] |- _ ]
      => destruct (cp_incl_dec cp1 cp2); try discriminate
    end. clear H0. unfold cp_incl in *. unfold high_comp_pat.
    intros c1 Hmatch'. specialize (c0 c1).
    unfold match_comp, NIExists.match_comp, Reflex.match_comp, match_comp_pf in *.
    simpl in *. unfold hdlr_term, CT, CTAG in *.
    destruct (COMPTDEC (comp_type COMPT COMPS c1)
                    (comp_pat_type COMPT COMPS
                       (Reflex.hdlr_term PAYD COMPT COMPS KSTD
                          (comp_type COMPT COMPS c)
                          (tag PAYD m)) envd cp)); try discriminate.
    simpl in *. destruct c1. destruct cp. simpl in *. destruct e.
    cut (shvec_match (projT2 (comp_conf_desc COMPT COMPS comp_type))
                  sdenote_desc sdenote_desc_conc_pat elt_match comp_conf
                  (get_conc_pat_conf (Reflex.comp_type COMPT COMPS c)
                     (tag PAYD m) envd
                     (projT1 (comp_conf_desc COMPT COMPS comp_type))
                     (projT2 (comp_conf_desc COMPT COMPS comp_type))
                     comp_pat_conf
                     (merge_all_cfgps (Reflex.comp_type COMPT COMPS c) l s)) = true).
      intro. rewrite H0 in *. simpl in *.
      destruct (COMPTDEC comp_type (conc_pat_type COMPT COMPS x)); try discriminate.
      destruct x. simpl in *. destruct e. unfold lblr_match_comp.
      apply existsb_exists. exists ({| conc_pat_type := comp_type; conc_pat_conf := conc_pat_conf |}).
      split; auto. unfold NIExists.match_comp, Reflex.match_comp, match_comp_pf. simpl.
      destruct (COMPTDEC comp_type comp_type); try intuition. rewrite UIP_refl with (p:=e). auto.
      clear c0. destruct (comp_conf_desc COMPT COMPS comp_type) as [n cfgd].
      induction n.
        auto.

        destruct cfgd. destruct comp_conf. destruct comp_pat_conf. simpl in *.
        destruct o.
          destruct d. destruct e.
    destruct x. simpl in *. destruct (COMPTDEC comp_type conc_pat_type).
    destruct e. destruct (comp_conf_desc COMPT COMPS comp_type).
    Check UIP_refl. rewrite UIP_refl with (p:=e) (x:=comp_pat_type COMPT COMPS
        (Reflex.hdlr_term PAYD COMPT COMPS KSTD (comp_type COMPT COMPS c)
           (tag PAYD m)) envd cp) in Hmatch'.
    induction l.
      simpl in *.

    destruct ((cp_incl_dec
               {|
               conc_pat_type := comp_pat_type COMPT COMPS
                                  (hdlr_term (comp_type COMPT COMPS c)
                                     (tag PAYD m)) envd cp;
               conc_pat_conf := get_conc_pat_conf (comp_type COMPT COMPS c)
                                  (tag PAYD m) envd
                                  (projT1
                                     (comp_conf_desc COMPT COMPS
                                        (comp_pat_type COMPT COMPS
                                           (hdlr_term
                                              (comp_type COMPT COMPS c)
                                              (tag PAYD m)) envd cp)))
                                  (projT2
                                     (comp_conf_desc COMPT COMPS
                                        (comp_pat_type COMPT COMPS
                                           (hdlr_term
                                              (comp_type COMPT COMPS c)
                                              (tag PAYD m)) envd cp)))
                                  (comp_pat_conf COMPT COMPS
                                     (hdlr_term (comp_type COMPT COMPS c)
                                        (tag PAYD m)) envd cp)
                                  (merge_all_cfgps
                                     (comp_type COMPT COMPS c) l s) |} x))).
  destruct (hd_error
    (get_candidate_pats clblr
      (comp_type COMPT COMPS c))) as [? | ?]_eqn; try discriminate. SearchAbout hd.
  induction clblr.
    discriminate.

    unfold high_comp_pat in *. intros c' Hmatch'. simpl in *.
    apply Bool.orb_prop in Hmatch. unfold is_high_comp_pat in *.
    simpl in *. destruct Hmatch.
      admit.

      rewrite IHclblr; auto. rewrite Bool.orb_true_r. auto.
  destruct cp as [ctp cfgp]. unfold lblr_match_comp in Hmatch.
  unfold is_high_comp_pat in *. unfold NIExists.match_comp, Reflex.match_comp, match_comp_pf in *.
  simpl in *. destruct (COMPTDEC (comp_type COMPT COMPS c') ctp); try discriminate.
  destruct e.
  induction clblr.
    discriminate.

    simpl in *.


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

Lemma vlblr_shift : forall n (vlblr:fin (S n) -> bool) (f:fin n),
  vlblr (Some f) = vlblr (shift_fin f).
(*  vlblr (Some f) = b -> vlblr (shift_fin f) = b.*)
Proof.
  intros n vlblr f.
  induction n.
    simpl in *. contradiction.

    simpl. destruct f; auto.
Qed.

Definition states_ok (s1 s2:kstate) clblr vlblr :=
  let clblr := lblr_match_comp COMPT COMPTDEC COMPS clblr in
  high_out_eq _ _ _ _ s1 s2 clblr /\
    vars_eq _ _ _ _ s1 s2 vlblr.

Definition cmd_ok_low c m envd cmd clblr vlblr :=
  forall env s i,
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = false ->
    states_ok s (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env;hdlr_kst:=s|})) clblr vlblr.

Definition cmd_ok_high c m envd cmd clblr vlblr llblr :=
  forall env1 env2 s1 s2 i,
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
    states_ok s1 s2 clblr vlblr ->
    locals_eq envd env1 env2 llblr ->
    states_ok
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env1;hdlr_kst:=s1|}))
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env2;hdlr_kst:=s2|}))
      clblr vlblr.

Lemma shvec_erase_ith : forall n vlblr
  (vd:svec (cdesc COMPT) n) v1 v2,
  shvec_erase (sdenote_cdesc COMPT COMPS) vlblr vd v1 =
  shvec_erase (sdenote_cdesc COMPT COMPS) vlblr vd v2 <->
  (forall i, vlblr i = true ->
    shvec_ith (sdenote_cdesc COMPT COMPS) vd v1 i =
    shvec_ith (sdenote_cdesc COMPT COMPS) vd v2 i).
Proof.
  intros n vlblr vd v1 v2.
  induction n.
    split; intros; auto.

    split.
      intros Heq i Hlblr.
      destruct vd; destruct i; simpl in *.
        destruct v1; destruct v2; simpl in *.
      apply IHn with (vlblr:=fun f => vlblr (shift_fin f));
        auto.
      match goal with
      | [ _ : context [ if ?e then _ else _ ] |- _ ]
        => destruct e
      end; inversion Heq; auto.
      rewrite <- vlblr_shift; auto.

      rewrite Hlblr in *. inversion Heq. auto.

      intro H. destruct vd. simpl.
      match goal with
      |- context [ if ?e then _ else _ ]
        => destruct e as [? | ?]_eqn
      end. f_equal. apply (H None Heqb).
      apply IHn; auto.
      intros i Hi.
      rewrite <- vlblr_shift in Hi.
      apply (H (Some i) Hi).

      f_equal. apply IHn; auto.
      intros i Hi.
      rewrite <- vlblr_shift in Hi.
      apply (H (Some i) Hi).
Qed.

Lemma hdlr_expr_ok_high_correct : forall c m (envd:vcdesc COMPT) cd
  (e:expr _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd cd)
  clblr vlblr llblr s1 s2 (env1 env2:sdenote_vcdesc _ _ envd),
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  states_ok s1 s2 clblr vlblr ->
  locals_eq envd env1 env2 llblr ->
  eval_hdlr_expr _ _ _ _ _ _ (kst _ _ _ _ s1) env1 e =
  eval_hdlr_expr _ _ _ _ _ _ (kst _ _ _ _ s2) env2 e.
Proof.
  intros c m envd cd e clblr vlblr llblr s1 s2 env1 env2 Hexpr Hstates Hlocals.
  induction e; simpl in *.
    induction t; simpl in *; auto; try discriminate.
      destruct b; simpl in *; auto; try discriminate.
      unfold locals_eq in Hlocals. destruct envd as [? envd]. simpl.
      eapply shvec_erase_ith with (vd:=envd) (i:=i); eauto.

      rewrite IHt; auto.

      destruct Hstates as [Hout Hvars]. unfold vars_eq in Hvars.
      destruct s1; destruct s2; destruct KSTD; simpl.
      eapply shvec_erase_ith with (vd:=v) (v1:=kst)
        (v2:=kst0) (i:=i); eauto.

    rewrite IHe; auto.

    apply andb_prop in Hexpr. destruct Hexpr.
    rewrite IHe1; auto. rewrite IHe2; auto.
Qed.

Lemma expr_list_ok_high_correct : forall c m (envd:vcdesc COMPT) cd
  (es:list (expr _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd cd))
  clblr vlblr llblr s1 s2 (env1 env2:sdenote_vcdesc _ _ envd),
  expr_list_ok_high _ _ _ _ es vlblr llblr = true ->
  states_ok s1 s2 clblr vlblr ->
  locals_eq envd env1 env2 llblr ->
  map (eval_hdlr_expr _ _ _ _ _ _ (kst _ _ _ _ s1) env1) es =
  map (eval_hdlr_expr _ _ _ _ _ _ (kst _ _ _ _ s2) env2) es.
Proof.
  intros c m envd cd es clblr vlblr llblr
    s1 s2 env1 env2 Hexpr Hstates Hlocals.
  induction es.
    auto.

    simpl in *.
    destruct (hdlr_expr_ok_high (CT COMPT COMPS c) (CTAG PAYD m) envd cd a vlblr
             llblr) as [? | ?]_eqn; try discriminate.
    erewrite hdlr_expr_ok_high_correct; eauto.
    rewrite IHes; auto.
Qed.

Lemma pl_hdlr_expr_ok_high_correct : forall c m (envd:vcdesc COMPT) vd
  (e:payload_expr _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd vd)
  clblr vlblr llblr s1 s2 (env1 env2:sdenote_vcdesc _ _ envd),
  pl_expr_ok_high _ _ _ _ (projT2 vd) e vlblr llblr = true ->
  states_ok s1 s2 clblr vlblr ->
  locals_eq envd env1 env2 llblr ->
  eval_hdlr_payload_expr _ _ _ _ _ _ (kst _ _ _ _ s1) _ env1 _ e =
  eval_hdlr_payload_expr _ _ _ _ _ _ (kst _ _ _ _ s2) _ env2 _ e.
Proof.
  intros c m envd vd e clblr vlblr llblr s1 s2 env1 env2 Hexpr Hstates Hlocals.
  destruct vd as [n vd].
  induction n.
    auto.

    destruct vd. destruct e.
    unfold eval_hdlr_payload_expr, eval_payload_expr, eval_payload_expr' in *.
    simpl in *. apply andb_prop in Hexpr. destruct Hexpr as [Hfst ?].
    eapply hdlr_expr_ok_high_correct in Hfst; eauto.
    unfold eval_hdlr_expr in Hfst. simpl in *. rewrite Hfst.
    f_equal. apply IHn; auto.
Qed.

Fixpoint all_cmd_ok_high c m envd
  cmd clblr vlblr llblr : Prop :=
  match cmd in Reflex.cmd _ _ _ _ _ _envd return
    (fin (projT1 _envd) -> bool) -> _
  with
  | Reflex.Seq _ cmd1 cmd2 => fun llblr =>
    all_cmd_ok_high c m _ cmd1 clblr vlblr llblr /\
    all_cmd_ok_high c m _ cmd2 clblr vlblr
      (get_llblr _ _ _ cmd1 vlblr llblr)
  | Reflex.Ite _ e cmd1 cmd2 => fun llblr =>
    if hdlr_expr_ok_high _ _ _ _ e vlblr llblr
    then all_cmd_ok_high c m _ cmd1 clblr vlblr llblr /\
      all_cmd_ok_high c m _ cmd2 clblr vlblr llblr
    else False
(*    all_cmd_ok_high c m _ cmd1 clblr vlblr llblr /\
    all_cmd_ok_high c m _ cmd2 clblr vlblr llblr*)
  | Reflex.CompLkup _ _ cmd1 cmd2 => fun llblr => False
(*    all_cmd_ok_high c m _ cmd1 clblr vlblr llblr /\
    all_cmd_ok_high c m _ cmd2 clblr vlblr llblr*)
  | _ => fun _ => cmd_ok_high c m envd cmd clblr vlblr llblr
  end llblr.

Definition cmd_ok_high' c m envd cmd clblr vlblr llblr :=
  forall env1 env2 s1 s2 i,
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
    states_ok s1 s2 clblr vlblr ->
    locals_eq envd env1 env2 llblr ->
    states_ok
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env1;hdlr_kst:=s1|}))
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env2;hdlr_kst:=s2|}))
      clblr vlblr /\
    locals_eq envd
      (hdlr_env _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env1;hdlr_kst:=s1|}))
      (hdlr_env _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env2;hdlr_kst:=s2|}))
      (get_llblr _ _ _ cmd vlblr llblr).

Lemma cmd_ok_high'_ok : forall c m envd cmd clblr vlblr llblr,
  cmd_ok_high' c m envd cmd clblr vlblr llblr ->
  cmd_ok_high c m envd cmd clblr vlblr llblr.
Proof.
  unfold cmd_ok_high, cmd_ok_high'. intros.
  apply H; auto.
Qed.

Lemma shvec_erase_wklblr : forall n lblr lblr'
  (vd:svec (cdesc COMPT) n) v1 v2,
  (forall i, implb (lblr' i) (lblr i) = true) ->
  shvec_erase (sdenote_cdesc COMPT COMPS) lblr vd v1 =
  shvec_erase (sdenote_cdesc COMPT COMPS) lblr vd v2 ->
  shvec_erase (sdenote_cdesc COMPT COMPS) lblr' vd v1 =
  shvec_erase (sdenote_cdesc COMPT COMPS) lblr' vd v2.
Proof.
  intros n lblr lblr' vd v1 v2 Himpl Herase.
  rewrite shvec_erase_ith. rewrite shvec_erase_ith in Herase.
  intros i Hlblr. apply Herase. specialize (Himpl i).
  rewrite Hlblr in Himpl. unfold implb in Himpl. auto.
Qed.

Lemma all_cmd_ok_high_correct : forall c m envd cmd clblr vlblr llblr,
  all_cmd_ok_high c m envd cmd clblr vlblr llblr ->
  cmd_ok_high' c m envd cmd clblr vlblr llblr.
Proof.
  intros c m envd cmd clblr vlblr llblr Hall_ok.
  unfold cmd_ok_high'.
  induction cmd; simpl in *; auto.
    intros. destruct Hall_ok as [Hall_ok1 Hall_ok2].
    match goal with
    |- context [ states_ok (hdlr_kst _ _ _ _ _
      (ve_st _ _ _ _ _ ?s1)) (hdlr_kst _ _ _ _ _
        (ve_st _ _ _ _ _ ?s2)) _ _ ]
     => destruct s1 as [s1' env1']_eqn; destruct s2 as [s2' env2']_eqn
    end. apply IHcmd2; auto.
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh.
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh0.
      simpl in *. subst s1'. subst s2'. destruct i. simpl.
      specialize (IHcmd1 llblr Hall_ok1 env1 env2 s1 s2 s H H0). apply IHcmd1; auto.
      apply f_equal with (f:=hdlr_env _ _ _ _ _)in Heqh.
      apply f_equal with (f:=hdlr_env _ _ _ _ _)in Heqh0.
      simpl in *. subst env1'. subst env2'. destruct i. simpl.
      specialize (IHcmd1 llblr Hall_ok1 env1 env2 s1 s2 s H H0). apply IHcmd1; auto.

    intros. destruct (hdlr_expr_ok_high (CT COMPT COMPS c)
    (CTAG PAYD m) envd (Desc COMPT num_d) e vlblr llblr) as [? | ?]_eqn.
    destruct Hall_ok as [Hall_ok1 Hall_ok2].
      erewrite hdlr_expr_ok_high_correct; eauto.
      destruct (num_eq
              (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
                 (kst PAYD COMPT COMPS KSTD s2) env2 e) FALSE).
      unfold locals_eq in *.
      split.
        eapply IHcmd2; eauto.
        apply shvec_erase_wklblr with
          (lblr:=get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2 vlblr
                llblr). intros.
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1 vlblr llblr i0);
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2 vlblr llblr i0);
          auto.
        apply IHcmd2; auto.

      unfold locals_eq in *.
      split.
        eapply IHcmd1; eauto.
        apply shvec_erase_wklblr with
          (lblr:=get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1 vlblr
                llblr). intros.
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2 vlblr llblr i0);
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1 vlblr llblr i0);
          auto.
        apply IHcmd1; auto.

      contradiction.

    unfold cmd_ok_high in *. simpl in *. auto.

    intros. split.
      unfold cmd_ok_high in *. simpl in *. auto.

      unfold locals_eq in *.
      apply shvec_erase_ith.
      destruct (pl_expr_ok_high (CT COMPT COMPS c) (CTAG PAYD m) envd
        (projT1 (comp_conf_desc COMPT COMPS t))
        (projT2 (comp_conf_desc COMPT COMPS t)) p vlblr llblr) as [? | ?]_eqn.
        erewrite pl_hdlr_expr_ok_high_correct; eauto.
        intros i' ?.
        destruct (fin_eq_dec i i').
          subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
          repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in H1. auto.

          intros i' ?. destruct (fin_eq_dec i i'); try discriminate; try contradiction.
          repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in H1.
          auto.

    intros. split.
      unfold cmd_ok_high in *. simpl in *. auto.

      unfold locals_eq in *.
      apply shvec_erase_ith.
      intros i' ?.
      destruct (fin_eq_dec i i').
        subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
        repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in H1. auto.

    unfold cmd_ok_high in *. simpl in *. auto.

    contradiction.
Qed.

(*Lemma get_llblr_correct : forall c m envd cmd i clblr vlblr llblr s1 s2,
  states_ok (hdlr_kst _ _ _ _ _ s1) (hdlr_kst _ _ _ _ _ s2) clblr vlblr ->
  locals_eq _ (hdlr_env _ _ _ _ _ s1) (hdlr_env _ _ _ _ _ s2) llblr ->
(*  all_cmd_ok_high c m envd cmd clblr vlblr llblr ->*)
  locals_eq _
    (hdlr_env _ _ _ _ _
      (ve_st c m envd cmd i s1))
    (hdlr_env _ _ _ _ _
      (ve_st c m envd cmd i s2))
    (get_llblr _ _ _ cmd vlblr llblr).
Proof.
  intros c m envd cmd i clblr vlblr llblr s1 s2
    Hstates Hlocals.
  generalize dependent s1.
  generalize dependent s2.
  induction cmd; auto.
    (*Seq*)
    intros s2 s1 Hstates Hlocals. simpl in *.
    destruct Hall_ok as [Hall_ok1 Hall_ok2].
    eapply IHcmd2; eauto.
    match goal with
      |- context [ve_st _ _ _ _ _ ?s]
        => let s' := fresh "s'" in
           let env' := fresh "env'" in
           destruct s as [s' env']
    end.
    destruct (ve_st c m envd cmd1 (fst i)
              {| hdlr_kst := s1; hdlr_env := env1 |}).
    destruct (ve_st c m envd cmd1 (fst i)
              {| hdlr_kst := s2; hdlr_env := env2 |})
      as [s2' env2']_eqn.
    destruct (ve_st c m envd cmd1 (fst i)
              {| hdlr_kst := s1; hdlr_env := env1 |})
      as [s1' env1']_eqn.
    eapply IHcmd2; eauto.
    apply f_equal with (f:=hdlr_env _ _ _ _ _) in Heqh.
    apply f_equal with (f:=hdlr_env _ _ _ _ _) in Heqh0.
    simpl in *. subst env1'. subst env2'. auto.
    apply f_equal with (f:=hdlr_kst _ _ _ _ _) in Heqh.
    apply f_equal with (f:=hdlr_kst _ _ _ _ _) in Heqh0.
    simpl in *. subst s1'. subst s2'. auto.

    (*Ite*)
    intros s2 s1 Hlocals; simpl in *.
    destruct s1; destruct s2. simpl.
    rewrite hdlr_expr_ok_high_correct with (s2:=hdlr_kst0)
      (env2:=hdlr_env0) (clblr:=clblr) (vlblr:=vlblr) (llblr:=llblr);
      auto.

    (*Spawn*)
    simpl. unfold locals_eq in *.
    apply shvec_erase_ith.
    destruct (pl_expr_ok_high (CT COMPT COMPS c) (CTAG PAYD m) envd
      (projT1 (comp_conf_desc COMPT COMPS t))
      (projT2 (comp_conf_desc COMPT COMPS t)) p vlblr llblr) as [? | ?]_eqn.
      erewrite pl_hdlr_expr_ok_high_correct; eauto.
      intros i' ?.
      destruct (fin_eq_dec i0 i').
        subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
        repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in Hlocals. auto.

      intros i' ?. destruct (fin_eq_dec i0 i'); try discriminate; try contradiction.
      repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in Hlocals.
      auto.

    (*Call*)
    simpl. unfold locals_eq in *.
    apply shvec_erase_ith.
    intros i' ?.
    destruct (fin_eq_dec i0 i').
      subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
      repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in Hlocals. auto.*)

Lemma stupd_low : forall clblr vlblr c m envd i e,
  vlblr i = false ->
  cmd_ok_low c m envd (StUpd _ _ i e) clblr vlblr.
Proof.
  intros clblr vlblr c m envd i e Hvar.
  split.
    unfold high_out_eq; simpl.
    intros tr tr' Htr Htr'. unfold NIExists.ktr in *.
    rewrite Htr in Htr'. apply pack_injective in Htr'.
    subst tr. auto.

    unfold vars_eq; simpl.
    generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
      (kst PAYD COMPT COMPS KSTD s) env e).
    simpl in *. clear e. intros.
    destruct s as [cs tr st].
    destruct KSTD as [n kstd].
    induction n.
      auto.

      destruct kstd. simpl in *.
      destruct i.
        match goal with
        |- context [ if ?e then _ else _ ]
          => destruct e
        end; simpl in *.
          f_equal. destruct st. simpl. apply IHn; auto.
          rewrite <- vlblr_shift; auto.

          f_equal. destruct st. simpl. apply IHn; auto.
          rewrite <- vlblr_shift; auto.

        unfold fin in *. rewrite Hvar. f_equal.
Qed.

Lemma stupd_high : forall c m envd i clblr vlblr llblr
  (e:expr COMPT (hdlr_term (CT _ _ c) (CTAG _ m)) envd _),
  vlblr i = false \/
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  cmd_ok_high c m envd (StUpd (hdlr_term (CT _ _ c) (CTAG _ m)) envd i e) clblr vlblr llblr.
Proof.
  intros c m envd i clblr vlblr llblr e H. destruct H as [Hlblr | Hexpr].
    split.
      unfold states_ok, high_out_eq in *. simpl. apply H0.

      unfold states_ok, vars_eq in *; simpl.
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s1) env1 e).
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s2) env2 e).
      simpl in *. clear e. intros.
      destruct s1 as [cs1 tr1 st1].
      destruct s2 as [cs2 tr2 st2].
      destruct KSTD as [n kstd].
      induction n.
        auto.

        destruct kstd. simpl in *. destruct H0.
        destruct i.
        match goal with
        |- context [ if ?e then _ else _ ]
          => destruct e
        end; simpl in *.
        inversion H2. f_equal. destruct st1. destruct st2.
        simpl. apply IHn; auto.
        rewrite <- vlblr_shift; auto.

        inversion H2. f_equal. destruct st1. destruct st2.
        simpl. apply IHn; auto.
        rewrite <- vlblr_shift; auto.

        unfold fin in *. rewrite Hlblr in *.
        inversion H2. simpl. f_equal. auto.

    split.

      unfold states_ok, high_out_eq in *. simpl. apply H0.

      unfold vars_eq in *; simpl.
      erewrite hdlr_expr_ok_high_correct
        with (env1:=env1) (env2:=env2); eauto.
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s2) env2 e).
      destruct s1; destruct s2. simpl in *. clear Hexpr e.
      simpl. destruct H0 as [Hout Hvars]. clear Hout.
      destruct KSTD as [n kstd]. unfold vars_eq in *.
      simpl in *. intros.
      induction n.
        auto.

        destruct kstd.
        destruct i; simpl in *;
          match goal with
          |- context [if ?e then _ else _ ]
            => destruct e
          end; inversion Hvars; f_equal;
          apply IHn; auto.
Qed.

Lemma stupd_high_all : forall c m envd i clblr vlblr llblr
  (e:expr COMPT (hdlr_term (CT _ _ c) (CTAG _ m)) envd _),
  vlblr i = false \/
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  all_cmd_ok_high c m envd (StUpd (hdlr_term (CT _ _ c) (CTAG _ m)) envd i e) clblr vlblr llblr.
Proof.
  apply stupd_high.
Qed.

Fixpoint match_all_cfg_pat n : forall (vd:svec desc n),
  shvec sdenote_desc_conc_pat vd :=
  match n as _n return
    forall (_vd:svec desc _n), shvec sdenote_desc_conc_pat _vd
  with
  | O => fun _ => tt
  | S n' => fun vd =>
    match vd with
    | (vd0, vd') =>
      (None, match_all_cfg_pat n' vd')
    end
  end.

Definition match_all_pat ct :=
  {| conc_pat_type:=ct
    ; conc_pat_conf:=match_all_cfg_pat _
    (projT2 (comp_conf_desc COMPT COMPS ct)) |}.

Lemma match_all_pat_correct : forall ct c,
  comp_type _ _ c = ct ->
  match_comp (match_all_pat ct) c = true.
Proof.
  intros ct c Hct. unfold match_all_pat.
  unfold match_comp, Reflex.match_comp, match_comp_pf.
  destruct (COMPTDEC (comp_type COMPT COMPS c)
           (conc_pat_type COMPT COMPS
              {|
              conc_pat_type := ct;
              conc_pat_conf := match_all_cfg_pat
                                 (projT1 (comp_conf_desc COMPT COMPS ct))
                                 (projT2 (comp_conf_desc COMPT COMPS ct)) |})); try contradiction.
  simpl in *. subst ct. rewrite UIP_refl with (p:=e).
  destruct c. simpl in *. destruct (comp_conf_desc COMPT COMPS comp_type) as [n cfg].
  induction n.
    auto.

    destruct cfg. destruct comp_conf. simpl in *. apply IHn.
Qed.
Require Import Sumbool.

Definition ct_not_in_clblr ct clblr :=
  forallb (fun cp => negb (projT1 (bool_of_sumbool
    (COMPTDEC ct (conc_pat_type COMPT COMPS cp))))) clblr = true.

Lemma not_in_clblr : forall ct clblr,
  ct_not_in_clblr ct clblr ->
  forall c, comp_type COMPT COMPS c = ct ->
    lblr_match_comp _ COMPTDEC _ clblr c = false.
Proof.
  intros ct clblr Hnot_in c Hct. unfold lblr_match_comp.
  induction clblr.
    auto.

    unfold lblr_match_comp in *.
    unfold ct_not_in_clblr in Hnot_in. simpl in *. apply andb_prop in Hnot_in.
    destruct Hnot_in.
    unfold NIExists.match_comp, Reflex.match_comp, match_comp_pf in *.
    destruct c. simpl in *. subst comp_type.
    destruct (COMPTDEC ct (conc_pat_type COMPT COMPS a)); try discriminate.
    rewrite Bool.orb_false_r. auto.
Qed.

Lemma send_low : forall c m envd clblr vlblr ct
  ce t ple,
  ct_not_in_clblr ct clblr ->
  cmd_ok_low c m envd (Send _ envd ct ce t ple) clblr vlblr.
Proof.
  intros c m envd clblr vlblr ct ce t ple Hnot_in.
  unfold cmd_ok_low, states_ok. intros.
  split.
    unfold high_out_eq. intros. destruct s as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. erewrite not_in_clblr; eauto.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m kst env ce). auto.

    unfold vars_eq. simpl. auto.
Qed.

Lemma send_low_ccomp : forall c m envd clblr vlblr t ple,
  cmd_ok_low c m envd (Send _ envd _
    (Term _ _ _ (CComp _ _ _ _ _ _ _)) t ple) clblr vlblr.
Proof.
  intros c m envd clblr vlblr t ple.
  unfold cmd_ok_low, states_ok. intros.
  split.
    unfold high_out_eq. intros. destruct s as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. rewrite H. auto.

    unfold vars_eq. simpl. auto.
Qed.

Lemma send_high_all : forall c m envd clblr vlblr llblr ct
  ce t ple,
  hdlr_expr_ok_high _ _ _ _ ce vlblr llblr = true ->
  pl_expr_ok_high _ _ _ _ _ ple vlblr llblr = true ->
  all_cmd_ok_high c m envd (Send _ envd ct ce t ple) clblr vlblr llblr.
Proof.
  simpl. unfold cmd_ok_high. unfold states_ok. simpl.
  intros c m envd clblr vlblr llblr ct ce t ple Hexpr
    Hpexpr env1 env2 s1 s2 i Hlblr Hstates Hlocals.
  split.
    unfold high_out_eq. intros tr tr' Htr Htr'.
    destruct s1 as [? [ ? ] ?]_eqn. destruct s2 as [? [ ? ] ?]_eqn. simpl in *.
    repeat uninhabit. simpl. inversion Heqk. inversion Heqk0.
    apply f_equal with (f:=Reflex.kst _ _ _ _) in Heqk.
    apply f_equal with (f:=Reflex.kst _ _ _ _) in Heqk0.
    simpl in *. rewrite <- Heqk. rewrite <- Heqk0.
    destruct Hstates as [Hout Hvars]. unfold high_out_eq in Hout.
    erewrite Hout; eauto.
    erewrite hdlr_expr_ok_high_correct with (s2:=s2) (clblr:=clblr); eauto.
    erewrite pl_hdlr_expr_ok_high_correct with (s2:=s2) (clblr:=clblr); eauto.
    subst s1. subst s2. unfold states_ok. auto.
    subst s1. subst s2. unfold states_ok. auto.

    unfold vars_eq in *. simpl. apply Hstates.
Qed.

Lemma send_high_all_low_comp : forall c m envd clblr vlblr llblr ct
  ce t ple,
  ct_not_in_clblr ct clblr ->
  all_cmd_ok_high c m envd (Send _ envd ct ce t ple) clblr vlblr llblr.
Proof.
  intros c m envd clblr vlblr llblr ct ce t ple Hnot_in.
  simpl. unfold cmd_ok_high, states_ok. intros.
  split.
    unfold high_out_eq in *. intros. destruct s1 as [? [?] ?]; destruct s2 as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. repeat erewrite not_in_clblr; eauto.
    destruct H0. auto.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m kst0 env2 ce). auto.
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m kst env1 ce). auto.

    unfold vars_eq. simpl. destruct H0. auto.
Qed.

Lemma call_low : forall c m envd clblr vlblr
  e es i EQ,
  cmd_ok_low c m envd (Call _ envd e es i EQ) clblr vlblr.
Proof.
  intros c m envd clblr vlblr e es i EQ.
  simpl. unfold cmd_ok_low. intros.
  unfold states_ok, high_out_eq, vars_eq in *. simpl.
  split.
    intros. destruct s as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. auto.

    auto.
Qed.

Lemma call_high_all : forall c m envd clblr vlblr llblr
  e es i EQ,
  all_cmd_ok_high c m envd (Call _ envd e es i EQ) clblr vlblr llblr.
Proof.
  intros c m envd clblr vlblr llblr e es i EQ.
  simpl. unfold cmd_ok_high. intros.
  unfold states_ok, high_out_eq, vars_eq in *. simpl.
  split.
    intros. destruct s1 as [? [?] ?]; destruct s2 as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. destruct H0. erewrite H0; eauto.

    apply H0.
Qed.

Lemma spawn_high_all : forall c m envd clblr vlblr llblr ct
  ple i EQ,
  pl_expr_ok_high _ _ _ _ _ ple vlblr llblr = true ->
  all_cmd_ok_high c m envd (Spawn _ envd ct ple i EQ) clblr vlblr llblr.
Proof.
  simpl. unfold cmd_ok_high. unfold states_ok. simpl.
  intros c m envd clblr vlblr llblr ct ple i EQ
    Hpexpr env1 env2 s1 s2 f Hlblr Hstates Hlocals.
  split.
    unfold high_out_eq. intros tr tr' Htr Htr'.
    destruct s1 as [? [ ? ] ?]_eqn. destruct s2 as [? [ ? ] ?]_eqn. simpl in *.
    repeat uninhabit. simpl. inversion Heqk. inversion Heqk0.
    apply f_equal with (f:=Reflex.kst _ _ _ _) in Heqk.
    apply f_equal with (f:=Reflex.kst _ _ _ _) in Heqk0.
    simpl in *. rewrite <- Heqk. rewrite <- Heqk0.
    destruct Hstates as [Hout Hvars]. unfold high_out_eq in Hout.
    erewrite Hout; eauto.
    erewrite pl_hdlr_expr_ok_high_correct with (s2:=s2) (clblr:=clblr); eauto.
    subst s1. subst s2. unfold states_ok. auto.

    unfold vars_eq in *. simpl. apply Hstates.
Qed.

Lemma ite_low : forall c m envd clblr vlblr
  e cmd1 cmd2,
  cmd_ok_low c m envd cmd1 clblr vlblr ->
  cmd_ok_low c m envd cmd2 clblr vlblr ->
  cmd_ok_low c m envd (Ite _ envd e cmd1 cmd2) clblr vlblr.
Proof.
  intros c m envd clblr vlblr e cmd1 cmd2 Hcmd1 Hcmd2.
  unfold cmd_ok_low in *. intros env s i. simpl.
  destruct (num_eq
              (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
                 (kst PAYD COMPT COMPS KSTD s) env e) FALSE); auto.
Qed.

Lemma ite_high_all : forall c m envd clblr vlblr llblr
  e cmd1 cmd2,
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  all_cmd_ok_high c m envd cmd1 clblr vlblr llblr ->
  all_cmd_ok_high c m envd cmd2 clblr vlblr llblr ->
  all_cmd_ok_high c m envd (Ite _ envd e cmd1 cmd2) clblr vlblr llblr.
Proof.
  intros c m envd clblr vlblr llblr e cmd1 cmd2 Hexpr Hcmd1 Hcmd2.
  simpl. rewrite Hexpr. auto.
Qed.

Lemma seq_low : forall clblr vlblr c m envd cmd1 cmd2,
  cmd_ok_low c m envd cmd1 clblr vlblr ->
  cmd_ok_low c m envd cmd2 clblr vlblr ->
  cmd_ok_low c m envd (Seq _ _ cmd1 cmd2) clblr vlblr.
Proof.
  intros clblr vlblr c m envd cmd1 cmd2 Hcmd1 Hcmd2.
  split.
    unfold cmd_ok_low, high_out_eq, ve_st, kstate_run_prog in *. simpl in *.
    intros. destruct i as [i1 i2]. specialize (Hcmd1 env s i1 H).
    destruct Hcmd1 as [Hout1 ?].
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s; hdlr_env := env |} cmd1 i1) as [st env']_eqn.
    specialize (Hcmd2 env' st i2 H). destruct Hcmd2 as [Hout2 ?].
    destruct st as [? [tr''] ?]. simpl in *. rewrite Hout1 with (tr':=tr''); auto.
    apply Hout2 with (tr:=tr'') (tr':=tr'); auto. rewrite <- Heqh. auto.

    unfold cmd_ok_low, vars_eq, ve_st, kstate_run_prog in *. simpl in *.
    destruct i as [i1 i2].
    specialize (Hcmd1 env s i1 H). destruct Hcmd1 as [? Hvar1].
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s; hdlr_env := env |} cmd1 i1) as [st env']_eqn.
    specialize (Hcmd2 env' st i2 H). destruct Hcmd2 as [? Hvar2].
    rewrite Hvar1. simpl in *. rewrite Heqh. apply Hvar2.
Qed.

Lemma seq_high_all : forall c m envd cmd1 cmd2 clblr vlblr llblr,
  all_cmd_ok_high c m envd cmd1 clblr vlblr llblr ->
  all_cmd_ok_high c m envd cmd2 clblr vlblr
    (get_llblr (CT _ _ c) (CTAG _ m) envd cmd1 vlblr llblr) ->
  all_cmd_ok_high c m envd (Seq _ _ cmd1 cmd2) clblr vlblr llblr.
Proof.
  simpl. auto.
Qed.
(*  intros c m envd cmd1 cmd2 clblr vlblr llblr Hcmd1 Hcmd2.
    unfold cmd_ok_high, high_out_eq, ve_st, kstate_run_prog in *. simpl in *.
    intros. destruct i as [i1 i2]. specialize (Hcmd1 env1 env2 s1 s2 i1 H H0).
    simpl in *.
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s1; hdlr_env := env1 |} cmd1 i1) as [s1' env1']_eqn.
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s2; hdlr_env := env2 |} cmd1 i1) as [s2' env2']_eqn.
    simpl in *.
    apply Hcmd2; intuition.
    apply f_equal with (f:=hdlr_env _ _ _ _ _) in Heqh.
    apply f_equal with (f:=hdlr_env _ _ _ _ _) in Heqh0.
    simpl in *. subst env1'. subst env2'.
    eapply get_llblr_correct; eauto.
Qed.*)

Lemma high_out_eq_inter_ve_st : forall c m s tr clblr,
  Reflex.ktr _ _ _ _ s = [tr]%inhabited ->
  high_out_eq _ _ _ _ s (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr) clblr.
Proof.
  unfold high_out_eq, mk_inter_ve_st. simpl. intros.
  remove_redundant_ktr. repeat uninhabit. auto.
Qed.

Lemma high_out_trans : forall (s1 s2 s3:kstate) clblr,
  high_out_eq _ _ _ _ s1 s2 clblr ->
  high_out_eq _ _ _ _ s2 s3 clblr ->
  high_out_eq _ _ _ _ s1 s3 clblr.
Proof.
  intros. unfold high_out_eq in *.
  intros. destruct s2. destruct ktr0.
  rewrite <- H0 with (tr:=k) (tr':=tr'); auto.
Qed.

Lemma high_out_eq_refl : forall (s:kstate) clblr,
  high_out_eq _ _ _ _ s s clblr.
Proof.
  intros. unfold high_out_eq. intros.
  remove_redundant_ktr. auto.
Qed.

Lemma vars_eq_refl : forall (s:kstate) vlblr,
  vars_eq _ _ _ _ s s vlblr.
Proof.
  auto.
Qed.

Lemma high_out_eq_sym : forall (s s':kstate) clblr,
  high_out_eq _ _ _ _ s s' clblr ->
  high_out_eq _ _ _ _ s' s clblr.
Proof.
  unfold high_out_eq. intros.
  symmetry. auto.
Qed.

Lemma vars_eq_sym : forall (s s':kstate) vlblr,
  vars_eq _ _ _ _ s s' vlblr ->
  vars_eq _ _ _ _ s' s vlblr.
Proof.
  unfold vars_eq. intros. auto.
Qed.

Lemma vars_eq_inter_ve_st : forall c m s tr clblr,
  Reflex.ktr _ _ _ _ s = [tr]%inhabited ->
  vars_eq _ _ _ _ s (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr) clblr.
Proof.
  auto.
Qed.

Lemma vars_eq_trans : forall (s1 s2 s3:kstate) clblr,
  vars_eq _ _ _ _ s1 s2 clblr ->
  vars_eq _ _ _ _ s2 s3 clblr ->
  vars_eq _ _ _ _ s1 s3 clblr.
Proof.
  intros. unfold vars_eq in *. etransitivity; eauto.
Qed.

Lemma nop_low : forall clblr vlblr c m envd,
  cmd_ok_low c m envd (Nop _ _) clblr vlblr.
Proof.
  intros clblr vlblr c m envd.
  unfold cmd_ok_low, states_ok. intros env s.
  simpl. split.
    apply high_out_eq_refl.
    apply vars_eq_refl.
Qed.

Lemma nop_high : forall clblr vlblr c m envd llblr,
  cmd_ok_high c m envd (Nop _ _) clblr vlblr llblr.
Proof.
  intros clblr vlblr c m envd llblr.
  unfold cmd_ok_high, states_ok. intros.
  simpl. auto.
Qed.

Lemma nop_high_all : forall clblr vlblr c m envd llblr,
  all_cmd_ok_high c m envd (Nop _ _) clblr vlblr llblr.
Proof.
  apply nop_high.
Qed.

Section WITH_HANDLERS_INIT.

Variable HANDLERS : handlers PAYD COMPT COMPS KSTD.
Variable INIT : init_prog PAYD COMPT COMPS KSTD IENVD.
Definition ValidExchange := Reflex.ValidExchange PAYD COMPT COMPTDEC COMPS KSTD HANDLERS.

Lemma prune_nop_1 : forall clblr vlblr c m i s s',
  ValidExchange c m i s s' ->
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  high_out_eq _ _ _ _ s s' clblr /\ vars_eq _ _ _ _ s s' vlblr.
Proof.
  intros clblr vlblr c m i s s' Hve Hnop.
  inversion Hve. clear Hve.
    subst s'0. unfold hdlrs. generalize i. rewrite Hnop.
    intros. simpl. unfold kstate_run_prog. unfold hdlr_state_run_cmd.
    simpl. split.
      unfold high_out_eq. intros. simpl in *.
      uninhabit. simpl. remove_redundant_ktr. auto.

      unfold vars_eq. simpl. auto.
Qed.

Lemma prune_nop_1' : forall clblr vlblr c m i s tr,
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  Reflex.ktr _ _ _ _ s = [tr]%inhabited ->
  high_out_eq _ _ _ _ s
    (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
    (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr)
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
    clblr /\
    vars_eq _ _ _ _ s
      (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
      (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
      (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr)
      (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
      vlblr.
Proof.
  intros.
  eapply prune_nop_1; eauto.
  econstructor; eauto.
Qed.

Lemma prune_nop_2 : forall clblr vlblr c m i s1 s1' s2 s2',
  ValidExchange c m i s1 s1' ->
  ValidExchange c m i s2 s2' ->
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  high_out_eq _ _ _ _ s1 s2 clblr -> vars_eq _ _ _ _ s1 s2 vlblr ->
  high_out_eq _ _ _ _ s1' s2' clblr /\ vars_eq _ _ _ _ s1' s2' vlblr.
Proof.
  intros clblr vlblr c m i s1 s2 s1' s2' Hve1 Hve2 Hnop Hout Hvars.
  inversion Hve1. inversion Hve2. clear Hve1. clear Hve2.
    subst s'0. subst s'. unfold hdlrs. unfold hdlrs0. generalize i. rewrite Hnop.
    intros. unfold kstate_run_prog. unfold hdlr_state_run_cmd.
    simpl. split.
      unfold high_out_eq. intros. simpl in *.
      repeat uninhabit. simpl. auto.

      unfold vars_eq. simpl. auto.
Qed.

Lemma prune_nop_2' : forall clblr vlblr c m i s1 s2 tr1 tr2,
  projT2 (HANDLERS (tag _ m) (comp_type COMPT COMPS c)) =
  Nop _ _ ->
  Reflex.ktr _ _ _ _ s1 = [tr1]%inhabited ->
  Reflex.ktr _ _ _ _ s2 = [tr2]%inhabited ->
  high_out_eq _ _ _ _ s1 s2 clblr -> vars_eq _ _ _ _ s1 s2 vlblr ->
  high_out_eq _ _ _ _
    (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
      (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
      (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s1 tr1)
      (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
      (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
      (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
      (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s2 tr2)
      (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
      clblr /\
    vars_eq _ _ _ _
      (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
      (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
      (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s1 tr1)
      (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
      (kstate_run_prog PAYD COMPT COMPTDEC COMPS KSTD c m
      (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
      (mk_inter_ve_st PAYD COMPT COMPS KSTD c m s2 tr2)
      (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) i)
      vlblr.
Proof.
  intros.
  eapply prune_nop_2; eauto;
  econstructor; eauto.
Qed.

Definition low_ok'' clblr vlblr := forall c m,
  lblr_match_comp COMPT COMPTDEC COMPS clblr c = false ->
  cmd_ok_low c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) clblr vlblr.

Definition high_ok'' clblr vlblr :=
  forall c m,
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
    cmd_ok_high c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    clblr vlblr (fun _ => true).

Definition high_ok_all clblr vlblr :=
  forall c m,
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
    all_cmd_ok_high c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    clblr vlblr (fun _ => true).

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

Theorem ni_suf'' : forall clblr vlblr,
  low_ok'' clblr vlblr ->
  high_ok'' clblr vlblr ->
  NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS clblr vlblr.
Proof.
  intros. apply ni_suf'.
  unfold low_ok', low_ok'', cmd_ok_low, states_ok, ve_st in *.
  intros.
  split.
    apply high_out_trans with (s2:=mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr); auto.
    apply high_out_eq_inter_ve_st; auto.
    apply H; auto.
    apply vars_eq_trans with (s2:=mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr); auto.
    apply H; auto.

  unfold high_ok', high_ok'', cmd_ok_high, states_ok, ve_st in *.
  intros. apply H0; auto.
  split.
    apply high_out_trans with (s2:=s1). apply high_out_eq_sym.
    apply high_out_eq_inter_ve_st; auto.
    apply high_out_eq_sym. apply high_out_trans with (s2:=s2).
    apply high_out_eq_sym. apply high_out_eq_inter_ve_st; auto.
    apply high_out_eq_sym; auto.

    apply vars_eq_trans with (s2:=s1). apply vars_eq_sym.
    apply vars_eq_inter_ve_st; auto.
    apply vars_eq_sym. apply vars_eq_trans with (s2:=s2).
    apply vars_eq_sym. apply vars_eq_inter_ve_st; auto.
    apply vars_eq_sym; auto.
Qed.

Theorem ni_suf_all : forall clblr vlblr,
  low_ok'' clblr vlblr ->
  high_ok_all clblr vlblr ->
  NI PAYD COMPT COMPTDEC COMPS
  IENVD KSTD INIT HANDLERS clblr vlblr.
Proof.
  intros. apply ni_suf''; auto.
    unfold high_ok''. intros. apply cmd_ok_high'_ok.
    apply all_cmd_ok_high_correct; auto.
Qed.

End WITH_HANDLERS_INIT.

End Prune.