Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexHVec.
Require Import ReflexVec.
Require Import ReflexFin.
Require Import ReflexDenoted.
Require Import ReflexIO.
Require Import List.

Require Import NIExists.
Require Import Ynot.

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
Definition ReachInter := NIExists.ReachInter PAYD COMPT COMPTDEC COMPS KSTD.
Definition comp := comp COMPT COMPS.
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
Definition CompLkup := Reflex.CompLkup PAYD COMPT COMPS KSTD.
Definition hdlr_term := Reflex.hdlr_term PAYD COMPT COMPS KSTD.
Definition base_term := Reflex.base_term COMPT.
Definition match_comp := Reflex.match_comp COMPT COMPTDEC COMPS.
Definition cmd := Reflex.cmd PAYD COMPT COMPS KSTD.

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
  (e:expr COMPT COMPS (hdlr_term ct mt) envd c) vlblr llblr :=
  match e with
  | Term _ t => hdlr_term_ok_high _ _ _ _ t vlblr llblr
  | UnOp _ _ _ e' => hdlr_expr_ok_high _ _ _ _ e' vlblr llblr
  | BinOp _ _ _ _ e1 e2 => andb (hdlr_expr_ok_high _ _ _ _ e1 vlblr llblr)
    (hdlr_expr_ok_high _ _ _ _ e2 vlblr llblr)
  end.

Definition hdlr_oexpr_ok_high ct mt envd c
  (oe:option (expr COMPT COMPS (hdlr_term ct mt) envd c))
  vlblr llblr :=
  match oe with
  | Some e => hdlr_expr_ok_high ct mt envd c e vlblr llblr
  | None => true
  end.

Definition expr_list_ok_high ct mt envd c
  (es:list (expr COMPT COMPS (hdlr_term ct mt) envd c)) vlblr llblr :=
  fold_right (fun e => andb
    (hdlr_expr_ok_high ct mt envd c e vlblr llblr)) true es.

Fixpoint pl_expr_ok_high ct mt envd n vd
  (ple:payload_expr' COMPT COMPS (hdlr_term ct mt) envd n vd) vlblr llblr :=
  match n as _n return
    forall (_vd:vdesc' _n) (ple:payload_expr' COMPT COMPS (hdlr_term ct mt) envd _n _vd), _
  with
  | O => fun _ _ => true
  | S n' => fun vd =>
    match vd as _vd return
      payload_expr' COMPT COMPS (hdlr_term ct mt) envd (S n') _vd -> _
    with
    | (vd0, vd') =>
      fun ple =>
        andb (hdlr_expr_ok_high ct mt envd _ (fst ple) vlblr llblr)
          (pl_expr_ok_high ct mt envd n' _ (snd ple) vlblr llblr)
    end
  end vd ple.

Fixpoint pl_oexpr_ok_high ct mt envd n vd
  (ple:payload_oexpr' COMPT COMPS (hdlr_term ct mt) envd n vd) vlblr llblr :=
  match n as _n return
    forall (_vd:vdesc' _n) (ple:payload_oexpr' COMPT COMPS (hdlr_term ct mt) envd _n _vd), _
  with
  | O => fun _ _ => true
  | S n' => fun vd =>
    match vd as _vd return
      payload_oexpr' COMPT COMPS (hdlr_term ct mt) envd (S n') _vd -> _
    with
    | (vd0, vd') =>
      fun ple =>
        andb (hdlr_oexpr_ok_high ct mt envd _ (fst ple) vlblr llblr)
          (pl_oexpr_ok_high ct mt envd n' _ (snd ple) vlblr llblr)
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
  | Reflex.CompLkup _ _ i' _ cmd1 cmd2 =>
    fun i =>
      if fin_eq_dec i i'
      then false
      else andb (get_writes _ _ cmd1 i)
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
Defined.

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
      specialize (c (comp_conf _ _ cp)).
      destruct (shvec_match
              (projT2 (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS cp)))
              sdenote_desc sdenote_desc_conc_pat elt_match
              (comp_conf COMPT COMPS cp) cfg1);
      destruct (shvec_match
              (projT2 (comp_conf_desc COMPT COMPS (comp_type COMPT COMPS cp)))
              sdenote_desc sdenote_desc_conc_pat elt_match
              (comp_conf COMPT COMPS cp) cfg2); auto.

      right. intro. contradict n. intro cfg. unfold cp_incl in *.
      specialize (H {|comp_type:=ct2; comp_fd:=devnull; comp_conf:=cfg|}).
      unfold match_comp, Reflex.match_comp, match_comp_pf in *. simpl in *.
      destruct (COMPTDEC ct2 ct2); auto.
      rewrite UIP_refl with (p:=e) in *.
      destruct (shvec_match (projT2 (comp_conf_desc COMPT COMPS ct2))
                 sdenote_desc sdenote_desc_conc_pat
                 elt_match cfg cfg1);
      destruct (shvec_match (projT2 (comp_conf_desc COMPT COMPS ct2))
                 sdenote_desc sdenote_desc_conc_pat
                 elt_match cfg cfg2); auto.

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
Defined.

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

Lemma compcd_inj : forall ct ct',
  Comp COMPT ct = Comp COMPT ct' ->
  ct = ct'.
Proof.
  intros. injection H. auto.
Defined.

Definition peval_hdlr_term {cd envd} ct mt (t : hdlr_term ct mt envd cd)
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
  destruct t.
    exact None.
    exact None.
refine (
  match t in Reflex.hdlr_term _ _ _ _ _ _ _ _c return
      _c = Comp COMPT ct' -> _
  with
  | CComp => fun EQ =>
    match compcd_inj _ _ EQ in _ = _ct return
      forall (i:fin (projT1 (comp_conf_desc COMPT COMPS _ct))),
      option
      (sdenote_cdesc COMPT COMPS
       (Desc COMPT (svec_ith (projT2 (comp_conf_desc COMPT COMPS _ct)) i)))
    with
    | Logic.eq_refl => fun i =>
      shvec_ith _ _ v i
    end i
  | _ => fun _ => None
  end (Logic.eq_refl _)).
      exact None.
    exact None.
Defined.

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
  intros cd envd ct mt t cfgp v cfg f pl Hpeval Hcfgp st env. Require Import Program.
  generalize dependent v. dependent inversion t; try discriminate.
  dependent destruction h; try discriminate. admit.
  generalize dependent h0. (* rewrite <- x.
  rewrite <- x0. generalize (Comp COMPT ct').

revert x0. generalize (svec_ith (projT2 KSTD) i0).
  intros c Heqc. dependent rewrite <- Heqc in h0.
  dependent rewrite <- x0 in h0.
  generalize dependent i.
  simpl.

dependent inversion h with (fun (hndx : cdesc COMPT)
(hterm : Reflex.hdlr_term PAYD COMPT COMPS KSTD ct mt envd hndx) =>

match hndx as _hndx return
  sdenote_cdesc COMPT COMPS _hndx ->
  Prop
with
| Comp ct1 => fun x =>

forall (i : fin (projT1 (comp_conf_desc COMPT COMPS ct1)))
     (v : sdenote_desc (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i)),
   match
     h in (Reflex.hdlr_term _ _ _ _ _ _ _ _c)
     return
       (_c = Comp COMPT ct' ->
        option
          (sdenote_desc
             (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i)))
   with
   | Base d _ => fun _ : d = Comp COMPT ct' => None
   | CComp =>
       fun EQ : Comp COMPT ct = Comp COMPT ct' =>
       match
         compcd_inj ct ct' EQ in (_ = _ct)
         return
           (forall i0 : fin (projT1 (comp_conf_desc COMPT COMPS _ct)),
            option
              (sdenote_desc
                 (svec_ith (projT2 (comp_conf_desc COMPT COMPS _ct)) i0)))
       with
       | eq_refl =>
           fun i0 : fin (projT1 (comp_conf_desc COMPT COMPS ct)) =>
           shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct)))
             cfgp i0
       end i
   | CConf ct'0 i0 _ =>
       fun
         _ : Desc COMPT
               (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct'0)) i0) =
             Comp COMPT ct' => None
   | MVar i0 =>
       fun
         _ : Desc COMPT (svec_ith (projT2 (lkup_tag PAYD mt)) i0) =
             Comp COMPT ct' => None
   | StVar i0 => fun _ : svec_ith (projT2 KSTD) i0 = Comp COMPT ct' => None
   end (eq_refl (Comp COMPT ct')) = Some v ->
   match
     projT2
       x in (_ = _ct)
     return
       (forall _i : fin (projT1 (comp_conf_desc COMPT COMPS _ct)),
        sdenote_desc (svec_ith (projT2 (comp_conf_desc COMPT COMPS _ct)) _i))
   with
   | eq_refl =>
       fun
         i0 : fin
                (projT1
                   (comp_conf_desc COMPT COMPS
                      (comp_type COMPT COMPS
                         (projT1
                            x)))) =>
       shvec_ith sdenote_desc
         (projT2
            (comp_conf_desc COMPT COMPS
               (comp_type COMPT COMPS
                  (projT1
                     x))))
         (comp_conf COMPT COMPS
            (projT1
               x)) i0
   end i = v

| _ => fun _ => True
end

(eval_hdlr_term PAYD COMPT COMPS KSTD
                  {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
                  {| tag := mt; pay := pl |} st h env)

).













































































forall i : fin (projT1 (comp_conf_desc COMPT COMPS ct1)),
   Desc COMPT (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i) = cd ->
   forall
     v : sdenote_cdesc COMPT COMPS
           (Desc COMPT (svec_ith (projT2 (comp_conf_desc COMPT COMPS ct1)) i)),
   y = Some v ->
match
     projT2 x in (_ = _ct)
     return
       (forall _i : fin (projT1 (comp_conf_desc COMPT COMPS _ct)),
        sdenote_desc (svec_ith (projT2 (comp_conf_desc COMPT COMPS _ct)) _i))
   with
   | eq_refl =>
       fun
         i0 : fin
                (projT1
                   (comp_conf_desc COMPT COMPS
                      (comp_type COMPT COMPS
                         (projT1 x)))) =>
       shvec_ith sdenote_desc
         (projT2
            (comp_conf_desc COMPT COMPS
               (comp_type COMPT COMPS
                  (projT1 x))))
         (comp_conf COMPT COMPS
            (projT1 x)) i0
   end i = v

| _ => fun _ => True
end

(eval_hdlr_term PAYD COMPT COMPS KSTD
                  {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
                  {| tag := mt; pay := pl |} st hterm env)

). simpl. discriminate. simpl. admit. simpl. generalize (shvec_ith (sdenote_cdesc COMPT COMPS) (projT2 KSTD) st i). generalize (svec_ith (projT2 KSTD) i).

  unfold eval_hdlr_term. simpl.
  simpl. Require Import Program. simpl. dependent destruction h; try discriminate. admit. dependent inversion h. unfold eval_hdlr_term; simpl
  intros v. 
  rewrite UIP_refl with (p:=compcd_inj ct' ct' eq_refl). intro Hpeval. simpl in *. auto.
(*apply JMeq_eq_dep in x; auto. apply eq_dep_eq_sigT in x. SearchAbout existT.
   inversion x.*)*)
  admit.
Qed.

Definition peval_expr {cd envd} ct mt
  (e:expr COMPT COMPS (hdlr_term ct mt) envd cd)
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
  (e:expr COMPT COMPS (hdlr_term ct mt) envd cd) cfgp v cfg f pl,
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
  (oe:option (expr COMPT COMPS (hdlr_term ct mt) envd cd))
  (v:shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))))
  : option (sdenote_cdesc COMPT COMPS cd).
destruct oe.
  exact (peval_expr ct mt e v).
  exact None.
Defined.

Lemma peval_oexpr_sound : forall cd envd ct mt
  (oe:option (expr COMPT COMPS (hdlr_term ct mt) envd cd)) cfgp v cfg f pl,
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
  payload_oexpr' COMPT COMPS (hdlr_term ct mt) envd n vd ->
  shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) ->
  shvec sdenote_desc_conc_pat vd.
intros vd cfgpe cfgp.
induction n.
  exact tt.

  simpl in *. destruct vd as [vd0 vd']. destruct cfgpe as [oe cfgpe'].
  exact (peval_oexpr ct mt oe cfgp, peval_payload_oexpr ct mt envd n vd' cfgpe' cfgp).
Defined.

Lemma peval_payload_oexpr_sound : forall envd ct mt vd
  (cfgpe:payload_oexpr' COMPT COMPS (hdlr_term ct mt) envd (projT1 vd) (projT2 vd))
  cfgp cfg f pl,
  (forall i v,
    shvec_ith sdenote_desc_conc_pat (projT2 (compd_conf (COMPS ct))) cfgp i =
    Some v ->
    shvec_ith sdenote_desc (projT2 (compd_conf (COMPS ct))) cfg i = v) ->
  (forall st env,
    cfgp_incl _
     (eval_hdlr_payload_oexpr PAYD COMPT COMPS KSTD
       (Build_comp COMPT COMPS ct f cfg)
       (Build_msg PAYD mt pl) st envd env vd cfgpe)
     (peval_payload_oexpr ct mt envd (projT1 vd) (projT2 vd) cfgpe cfgp)).
Proof.
  intros envd ct mt vd cfgpe cfgp cfg f pl Hcfgp st env cfg'.
  apply Bool.leb_implb. unfold Bool.leb.
  match goal with
  |- if ?e then _ else _ =>
    destruct e as [? | ?]_eqn; auto
  end. destruct vd as [n vd].
  induction n.
    auto.

    destruct vd. destruct cfgpe. destruct cfg'. simpl in *.
    apply andb_prop in Heqb. destruct Heqb.
    destruct (peval_oexpr ct mt o cfgp) as [? | ?]_eqn.
      rewrite peval_oexpr_sound with (v:=s2) (cfgp:=cfgp) in H; auto.
      rewrite H. simpl. apply IHn; auto.

      simpl. apply IHn; auto.
Qed.

Definition desc_eq_dec {d:desc} :
  forall (e1 e2:s[[d]]), decide (e1 = e2) :=
  match d with
  | num_d => num_eq
  | str_d => str_eq
  | fd_d  => fd_eq
  end.

Definition elt_incl_bool {d:desc} (oelt1 oelt2:option s[[d]]) : bool :=
  match oelt2 with
  | Some e1 =>
    match oelt1 with
    | Some e2 => if desc_eq_dec e1 e2 then true else false
    | None    => false
    end
  | None    => true
  end.

Lemma elt_incl_bool_sound : forall (d:desc) (oelt1 oelt2:option s[[d]]),
  elt_incl_bool oelt1 oelt2 = true ->
  elt_incl d oelt1 oelt2.
Proof.
  unfold elt_incl, elt_incl_bool, desc_eq_dec. intros d oelt1 oelt2 Hincl elt.
  unfold elt_match. destruct oelt2; destruct oelt1; destruct d; auto;
    repeat match goal with
    | [ |- context [num_eq ?e1 ?e2] ]
      => destruct (num_eq e1 e2)
    | [ _ : context [num_eq ?e1 ?e2] |- _ ]
      => destruct (num_eq e1 e2)
    | [ |- context [str_eq ?e1 ?e2] ]
      => destruct (str_eq e1 e2)
    | [ _ : context [str_eq ?e1 ?e2] |- _ ]
      => destruct (str_eq e1 e2)
    | [ |- context [fd_eq ?e1 ?e2] ]
      => destruct (fd_eq e1 e2)
    | [ _ : context [fd_eq ?e1 ?e2] |- _ ]
      => destruct (fd_eq e1 e2)
    end; intuition congruence.
Qed.

Fixpoint cfgp_incl_bool (n:nat) :
  forall (vd:svec desc n) (v1 v2:shvec sdenote_desc_conc_pat vd), bool :=
  match n with
  | O => fun _ _ _ => true
  | S n' => fun vd =>
    match vd with
    | (vd0, vd') => fun v1 v2 =>
      andb (elt_incl_bool (fst v1) (fst v2))
           (cfgp_incl_bool n' vd' (snd v1) (snd v2))
    end
  end.

Lemma cfgp_incl_bool_sound : forall (n:nat)
  (vd:svec desc n) (v1 v2:shvec sdenote_desc_conc_pat vd),
  cfgp_incl_bool n vd v1 v2 = true ->
  cfgp_incl (existT _ n vd) v1 v2.
Proof.
  intros n vd v1 v2 Hincl cfg.
  induction n.
    auto.

    destruct vd; destruct v1; destruct v2;
      destruct cfg; simpl in *. apply andb_prop in Hincl.
      destruct Hincl as [Helt_incl Hrest_incl].
      apply elt_incl_bool_sound in Helt_incl.
      unfold elt_incl in *; simpl in *.
      specialize (Helt_incl s4).
      repeat match goal with
             |- context[elt_match ?d ?e1 ?e2] =>
               destruct (elt_match d e1 e2)
             end; simpl; auto; discriminate.
Qed.

Check cp_incl_dec.

Definition is_high_comp_pat ct mt envd cp clblr cfgp : bool :=
  let conf := peval_payload_oexpr ct _ _ _ _
    (comp_pat_conf COMPT COMPS (hdlr_term ct mt) envd cp) 
    cfgp in
  let cpt := comp_pat_type _ _ _ _ cp in
  match clblr cpt with
  | Some cpcfgp =>
    projT1 (bool_of_sumbool (cp_incl_dec (Build_conc_pat COMPT COMPS cpt conf)
      (Build_conc_pat COMPT COMPS cpt cpcfgp)))
  | None => false
  end.

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

Lemma high_comp_cfgp_sound' : forall n vd v (i:fin n) cfg s,
  shvec_match vd sdenote_desc sdenote_desc_conc_pat
    elt_match cfg v = true ->
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

Lemma high_comp_cfgp_sound : forall ct f cfg clblr,
  lblr_match_comp COMPT COMPTDEC COMPS clblr
  {| comp_type := ct; comp_fd := f; comp_conf := cfg |} = true ->
  match clblr ct with
  | Some cfgp =>
    (forall (i : fin (projT1 (comp_conf_desc COMPT COMPS ct)))
      (v : s[[svec_ith (projT2 (comp_conf_desc COMPT COMPS ct)) i]]),
      shvec_ith sdenote_desc_conc_pat (projT2 (comp_conf_desc COMPT COMPS ct))
      cfgp i = Some v ->
      shvec_ith sdenote_desc (projT2 (comp_conf_desc COMPT COMPS ct)) cfg i = v)
  | None => True
  end.
Proof.
  intros ct f cfg clblr Hlblr.
  unfold lblr_match_comp, match_comp,
    Reflex.match_comp, match_comp_pf in Hlblr. simpl in *.
  destruct (clblr ct); auto.
  destruct (COMPTDEC ct ct); try discriminate.
  rewrite UIP_refl with (p:=e) in Hlblr. intros.
  apply high_comp_cfgp_sound' with (v:=s); auto.
  match goal with
  |- ?e = true =>
    destruct e; try discriminate; auto
  end.
Qed.

Lemma is_high_comp_pat_sound : forall c m envd cp cfgp clblr,
  lblr_match_comp COMPT COMPTDEC COMPS clblr c = true ->
  clblr (comp_type _ _ c) = Some cfgp ->
  is_high_comp_pat (comp_type _ _ c) (tag _ m) envd cp clblr cfgp = true ->
  forall st env,
    high_comp_pat COMPT COMPTDEC COMPS
      (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD c m st envd env cp)
      (lblr_match_comp COMPT COMPTDEC COMPS clblr).
Proof.
  Local Opaque cp_incl_dec.
  intros c m envd cp cfgp clblr Hmatch Hcfgp Hhigh st env.
  unfold is_high_comp_pat in Hhigh.
  destruct cp as [cpt cpfg]. destruct c as [ct f cfg].
  destruct m as [mt pl]. simpl in *.
  unfold high_comp_pat. intros c' Hmatch'.
  destruct (clblr cpt) as [ ? | ? ]_eqn; try discriminate.
  match goal with
  | [ _ : context [ cp_incl_dec ?cp1 ?cp2 ] |- _ ]
    => destruct (cp_incl_dec cp1 cp2); try discriminate
  end. unfold cp_incl in *. clear Hhigh. specialize (c c').
  unfold match_comp, Reflex.match_comp, match_comp_pf in *.
  simpl in *. unfold hdlr_term, CT, CTAG in *.
  destruct c' as [ct' ? ?]. simpl in *.
  destruct (COMPTDEC ct' cpt); try discriminate.
  subst ct'.
  pose proof (high_comp_cfgp_sound ct f cfg clblr Hmatch).
  rewrite Hcfgp in *.
  pose proof (peval_payload_oexpr_sound envd ct mt _
    cpfg cfgp cfg f pl H st env).
  unfold lblr_match_comp, Reflex.match_comp, match_comp_pf. simpl in *.
  destruct (COMPTDEC cpt cpt); try intuition.
  rewrite UIP_refl with (p:=e). rewrite Heqo.
  unfold cfgp_incl in *. simpl in *. specialize (H0 comp_conf).
  destruct
    (shvec_match
           (projT2 (comp_conf_desc COMPT COMPS cpt))
           sdenote_desc sdenote_desc_conc_pat elt_match
           comp_conf
           (eval_hdlr_payload_oexpr PAYD COMPT COMPS KSTD
              {| comp_type := ct; comp_fd := f; comp_conf := cfg |}
              {| tag := mt; pay := pl |} st envd env
              (comp_conf_desc COMPT COMPS cpt) cpfg));
    try discriminate. simpl in *. rewrite H0 in *. auto.
Qed.

Definition lift_llblr n llblr b : fin (S n) -> bool :=
  fun i => 
    match fin_eq_dec i (max_fin n) with
    | left _ => b
    | right H => llblr (proj_fin_ok i H)
    end.

Fixpoint get_llblr ct mt envd cmd cfgp clblr vlblr llblr :=
  match cmd in Reflex.cmd _ _ _ _ _ _envd return
    (fin (projT1 _envd) -> bool) -> _
  with
  | Reflex.Seq _ cmd1 cmd2 => fun llblr =>
    let llblr1 := get_llblr ct mt _ cmd1 cfgp clblr vlblr llblr in
    get_llblr ct mt _ cmd2 cfgp clblr vlblr llblr1
  | Reflex.Ite envd e cmd1 cmd2 => fun llblr =>
    if hdlr_expr_ok_high ct mt envd _ e vlblr llblr
    then fun i => andb (get_llblr ct mt _ cmd1 cfgp clblr vlblr llblr i)
      (get_llblr ct mt _ cmd2 cfgp clblr vlblr llblr i)
    else fun i => andb (get_writes _ _ cmd1 i) (get_writes _ _ cmd2 i)
  | Reflex.CompLkup envd cp i' EQ cmd1 cmd2 => fun llblr =>
    if andb (is_high_comp_pat ct mt _ cp clblr cfgp)
         (pl_oexpr_ok_high ct mt _ _ _
           (comp_pat_conf _ _ _ _ cp) vlblr llblr)
    then fun i => andb
      (get_llblr ct mt _ cmd1 cfgp clblr vlblr
        (fun i => if fin_eq_dec i i' then true else llblr i) i)
      (get_llblr ct mt _ cmd2 cfgp clblr vlblr llblr i)
    else fun i => andb (get_writes _ _ cmd1 i) (get_writes _ _ cmd2 i)
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
    ReachInter s ->
    lblr_match_comp COMPT COMPTDEC COMPS clblr c = false ->
    states_ok s (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env;hdlr_kst:=s|})) clblr vlblr.

Definition cmd_ok_high c m envd cmd clblr vlblr llblr
  (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true) :=
  forall env1 env2 s1 s2 i,
    ReachInter s1 -> ReachInter s2 ->
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
  (e:expr _ _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd cd)
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

Lemma hdlr_oexpr_ok_high_correct : forall c m (envd:vcdesc COMPT) cd
  (oe:option (expr _ _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd cd))
  clblr vlblr llblr s1 s2 (env1 env2:sdenote_vcdesc _ _ envd),
  hdlr_oexpr_ok_high _ _ _ _ oe vlblr llblr = true ->
  states_ok s1 s2 clblr vlblr ->
  locals_eq envd env1 env2 llblr ->
  eval_oexpr COMPT COMPS (hdlr_term (CT _ COMPS c) (CTAG PAYD m))
    (fun d envd env t =>
      eval_hdlr_term PAYD COMPT COMPS KSTD
      c m (kst _ _ _ _ s1) t env) env1 oe =
  eval_oexpr COMPT COMPS (hdlr_term (CT _ COMPS c) (CTAG PAYD m))
    (fun d envd env t =>
      eval_hdlr_term PAYD COMPT COMPS KSTD
      c m (kst _ _ _ _ s2) t env) env2 oe.
Proof.
  intros c m envd cd oe clblr vlblr llblr s1 s2 env1 env2 Hexpr Hstates Hlocals.
  destruct oe.
    simpl in *. f_equal.
    apply (hdlr_expr_ok_high_correct c m envd cd e
      clblr vlblr llblr s1 s2 env1 env2); auto.

    auto.
Qed.

Lemma expr_list_ok_high_correct : forall c m (envd:vcdesc COMPT) cd
  (es:list (expr _ _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd cd))
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
  (e:payload_expr _ _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd vd)
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

Lemma pl_hdlr_oexpr_ok_high_correct : forall c m (envd:vcdesc COMPT) vd
  (oe:payload_oexpr _ _ (hdlr_term (CT _ COMPS c) (CTAG PAYD m)) envd vd)
  clblr vlblr llblr s1 s2 (env1 env2:sdenote_vcdesc _ _ envd),
  pl_oexpr_ok_high _ _ _ _ (projT2 vd) oe vlblr llblr = true ->
  states_ok s1 s2 clblr vlblr ->
  locals_eq envd env1 env2 llblr ->
  eval_hdlr_payload_oexpr _ _ _ _ _ _ (kst _ _ _ _ s1) _ env1 _ oe =
  eval_hdlr_payload_oexpr _ _ _ _ _ _ (kst _ _ _ _ s2) _ env2 _ oe.
Proof.
  intros c m envd vd e clblr vlblr llblr s1 s2 env1 env2 Hexpr Hstates Hlocals.
  destruct vd as [n vd].
  induction n.
    auto.

    destruct vd. destruct e.
    unfold eval_hdlr_payload_oexpr, eval_payload_oexpr, eval_payload_oexpr' in *.
    simpl in *. apply andb_prop in Hexpr. destruct Hexpr as [Hfst ?].
    eapply hdlr_oexpr_ok_high_correct in Hfst; eauto.
    simpl in *. f_equal. auto.
    apply IHn; auto.
Qed.

Definition get_ccomp_cfgp c clblr
  (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true) :
  shvec sdenote_desc_conc_pat (projT2 (compd_conf (COMPS (comp_type _ _ c)))).
unfold lblr_match_comp in Hmatch.
destruct (clblr (comp_type _ _ c)).
  exact s.
  discriminate.
Defined.

Lemma get_ccomp_cfgp_correct : forall c clblr
  (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true),
  clblr (comp_type COMPT COMPS c) = Some (get_ccomp_cfgp c clblr Hmatch).
Proof.
  intros c clblr Hmatch.
  unfold lblr_match_comp in Hmatch.
  destruct c as [ct ? ?]. simpl in *. unfold get_ccomp_cfgp.
  simpl. destruct (clblr ct); auto; discriminate.
Qed.

Fixpoint all_cmd_ok_high c m envd
  cmd clblr vlblr llblr
  (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true) : Prop :=
  let ccfgp := get_ccomp_cfgp c clblr Hmatch in
  match cmd in Reflex.cmd _ _ _ _ _ _envd return
    (fin (projT1 _envd) -> bool) -> _
  with
  | Reflex.Seq _ cmd1 cmd2 => fun llblr =>
    all_cmd_ok_high c m _ cmd1 clblr vlblr llblr Hmatch /\
    all_cmd_ok_high c m _ cmd2 clblr vlblr
      (get_llblr _ _ _ cmd1 ccfgp clblr vlblr llblr) Hmatch
  | Reflex.Ite _ e cmd1 cmd2 => fun llblr =>
    if hdlr_expr_ok_high _ _ _ _ e vlblr llblr
    then all_cmd_ok_high c m _ cmd1 clblr vlblr llblr Hmatch /\
      all_cmd_ok_high c m _ cmd2 clblr vlblr llblr Hmatch
    else False
  | Reflex.CompLkup _ cp i' EQ cmd1 cmd2 => fun llblr =>
    if andb (is_high_comp_pat (comp_type _ _ c) (tag _ m) _ cp clblr ccfgp)
         (pl_oexpr_ok_high (comp_type _ _ c) (tag _ m) _ _ _
           (comp_pat_conf _ _ _ _ cp) vlblr llblr)
    then all_cmd_ok_high c m _ cmd1 clblr vlblr
      (fun i => if fin_eq_dec i i' then true else llblr i) Hmatch /\
      all_cmd_ok_high c m _ cmd2 clblr vlblr llblr Hmatch
    else False
  | _ => fun _ => cmd_ok_high c m envd cmd clblr vlblr llblr Hmatch
  end llblr.

Definition cmd_ok_high' c m envd cmd clblr vlblr llblr
  (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true) :=
  forall env1 env2 s1 s2 i,
    ReachInter s1 -> ReachInter s2 ->
    states_ok s1 s2 clblr vlblr ->
    locals_eq envd env1 env2 llblr ->
    states_ok
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env1;hdlr_kst:=s1|}))
      (hdlr_kst _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env2;hdlr_kst:=s2|}))
      clblr vlblr /\
    locals_eq envd
      (hdlr_env _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env1;hdlr_kst:=s1|}))
      (hdlr_env _ _ _ _ _ (ve_st c m envd cmd i {|hdlr_env:=env2;hdlr_kst:=s2|}))
      (get_llblr _ _ _ cmd (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr).

Lemma cmd_ok_high'_ok : forall c m envd cmd clblr vlblr llblr Hmatch,
  cmd_ok_high' c m envd cmd clblr vlblr llblr Hmatch ->
  cmd_ok_high c m envd cmd clblr vlblr llblr Hmatch.
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

Lemma all_cmd_ok_high_correct : forall c m envd cmd clblr vlblr llblr Hmatch,
  all_cmd_ok_high c m envd cmd clblr vlblr llblr Hmatch ->
  cmd_ok_high' c m envd cmd clblr vlblr llblr Hmatch.
Proof.
  intros c m envd cmd clblr vlblr llblr Hmatch Hall_ok. unfold cmd_ok_high'.
  induction cmd; simpl in *; try abstract auto.
    abstract (
    intros; destruct Hall_ok as [Hall_ok1 Hall_ok2];
    match goal with
    |- context [ states_ok (hdlr_kst _ _ _ _ _
      (ve_st _ _ _ _ _ ?s1)) (hdlr_kst _ _ _ _ _
        (ve_st _ _ _ _ _ ?s2)) _ _ ]
     => destruct s1 as [s1' env1']_eqn; destruct s2 as [s2' env2']_eqn
    end; apply IHcmd2; auto;
      try (
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh;
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh0;
      simpl in *; subst s1'; subst s2'; destruct i; simpl;
      specialize (IHcmd1 llblr Hall_ok1 env1 env2 s1 s2 s H H0);
      apply IHcmd1; auto);
      try (
      apply f_equal with (f:=hdlr_env _ _ _ _ _)in Heqh;
      apply f_equal with (f:=hdlr_env _ _ _ _ _)in Heqh0;
      simpl in *; subst env1'; subst env2'; destruct i; simpl;
      specialize (IHcmd1 llblr Hall_ok1 env1 env2 s1 s2 s H H0); apply IHcmd1; auto);
      try (
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh;
        unfold ve_st in Heqh; simpl in Heqh; subst s1';
          destruct i; simpl; destruct s1 as [? [k] ?];
            apply ReachInter_run with (tr:=k); auto);
      try (
      apply f_equal with (f:=hdlr_kst _ _ _ _ _)in Heqh0;
        unfold ve_st in Heqh0; simpl in Heqh0; subst s2';
          destruct i; simpl; destruct s2 as [? [k] ?];
            apply ReachInter_run with (tr:=k); auto)).

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
          (lblr:=get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2
            (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
                llblr). intros.
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr i0);
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2 
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr i0);
          auto.
        apply IHcmd2; auto.

      unfold locals_eq in *.
      split.
        eapply IHcmd1; eauto.
        apply shvec_erase_wklblr with
          (lblr:=get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1
            (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
                llblr). intros.
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd2
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr i0);
        destruct (get_llblr (CT COMPT COMPS c) (CTAG PAYD m) envd cmd1
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr i0);
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
          repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in H2. auto.

          intros i' ?. destruct (fin_eq_dec i i'); try discriminate; try contradiction.
          repeat rewrite shvec_ith_replace_cast_other; auto. rewrite shvec_erase_ith in H2.
          auto.

    intros. split.
      unfold cmd_ok_high in *. simpl in *. auto.
    
      unfold locals_eq in *.
      apply shvec_erase_ith.
      intros i' ?.
      destruct (fin_eq_dec i i').
        subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
        repeat rewrite shvec_ith_replace_cast_other; auto.
        rewrite shvec_erase_ith in H2. auto.

    unfold cmd_ok_high in *. simpl in *. auto.

    unfold CT, CTAG in *. simpl in *. intros.
    destruct (is_high_comp_pat (comp_type COMPT COMPS c) 
      (tag PAYD m) envd cp clblr (get_ccomp_cfgp c clblr Hmatch))
      as [? | ?]_eqn; try contradiction.
    unfold hdlr_term in *.
    match goal with
    | [ _ : context[pl_oexpr_ok_high ?a ?b ?c ?d ?e ?f ?g ?h] |- _ ]
      => destruct (pl_oexpr_ok_high a b c d e f g h) as [? | ?]_eqn;
        try contradiction
    end.
    destruct Hall_ok as [Hall_ok1 Hall_ok2]. intros.
      unfold eval_hdlr_comp_pat. destruct cp as [cpt cpconf]_eqn. simpl.
      rewrite (pl_hdlr_oexpr_ok_high_correct c m envd _
        cpconf clblr vlblr llblr s1 s2 env1 env2); auto.
      rewrite (hout_eq_find_eq PAYD COMPT COMPTDEC COMPS KSTD
        ({|
            conc_pat_type := cpt;
            conc_pat_conf := eval_hdlr_payload_oexpr PAYD COMPT COMPS KSTD c
                               m (kst PAYD COMPT COMPS KSTD s2) envd env2
                               (comp_conf_desc COMPT COMPS cpt) cpconf |})
        s1 s2 (lblr_match_comp COMPT COMPTDEC COMPS clblr)); auto.
      match goal with
      |- context [find_comp ?a ?b ?c ?d ?e] =>
        destruct (find_comp a b c d e)
      end.
        unfold locals_eq in *.
        split.
          eapply IHcmd1; eauto.
            destruct s1; auto.
            destruct s2; eauto.
            apply shvec_erase_ith. intros i' ?.
            destruct (fin_eq_dec i' i).
              subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
              repeat rewrite shvec_ith_replace_cast_other; auto.
              rewrite shvec_erase_ith in H2. auto.

          apply shvec_erase_wklblr with
            (lblr:=get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd1
              (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
              (fun i1 : fin (projT1 envd) =>
                if fin_eq_dec i1 i then true else llblr i1)). intros.
          destruct ((get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd1
            (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
            (fun i2 : fin (projT1 envd) =>
              if fin_eq_dec i2 i then true else llblr i2) i1)); auto.
          destruct (get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd2
            (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
            llblr i1); auto.
          eapply IHcmd1; eauto.
          destruct s1; auto. destruct s2; auto.
          apply shvec_erase_ith. intros i' ?.
          destruct (fin_eq_dec i' i).
            subst i'. repeat rewrite shvec_ith_replace_cast_ith. auto.
            repeat rewrite shvec_ith_replace_cast_other; auto.
            rewrite shvec_erase_ith in H2; auto.

      split.
        eapply IHcmd2; eauto.

        unfold locals_eq in *.
        apply shvec_erase_wklblr with
          (lblr:=get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd2
            (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
            llblr). intros.
        destruct (get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd2
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
          llblr i1);
        destruct (get_llblr (comp_type COMPT COMPS c) (tag PAYD m) envd cmd1
          (get_ccomp_cfgp c clblr Hmatch) clblr vlblr
          (fun i2 : fin (projT1 envd) =>
            if fin_eq_dec i2 i then true else llblr i2) i1); auto.
        eapply IHcmd2; eauto.

      apply H1.

      pose proof (is_high_comp_pat_sound c m envd cp (get_ccomp_cfgp c clblr Hmatch) clblr) as Hgoal.
      unfold eval_hdlr_comp_pat in *. subst cp. apply Hgoal; auto.
      apply get_ccomp_cfgp_correct.
Qed.

Lemma complkup_low : forall c m envd clblr vlblr
  cp i EQ cmd1 cmd2,
  cmd_ok_low c m envd cmd1 clblr vlblr ->
  cmd_ok_low c m envd cmd2 clblr vlblr ->
  cmd_ok_low c m envd (CompLkup _ envd cp i EQ cmd1 cmd2) clblr vlblr.
Proof.
  intros c m envd clblr vlblr cp i EQ cmd1 cmd2 Hcmd1 Hcmd2.
  unfold cmd_ok_low in *. intros. simpl.
  destruct (find_comp COMPT COMPTDEC COMPS
            (eval_hdlr_comp_pat PAYD COMPT COMPS KSTD c m
               (kst PAYD COMPT COMPS KSTD s) envd env cp)
            (kcs PAYD COMPT COMPS KSTD s)); auto.
  destruct s; auto.
Qed.

Lemma complkup_high_all : forall c m envd clblr vlblr llblr
  cp i EQ cmd1 cmd2 Hmatch,
  is_high_comp_pat (comp_type _ _ c) (tag _ m) _ cp clblr
    (get_ccomp_cfgp c clblr Hmatch) = true ->
  pl_oexpr_ok_high (comp_type _ _ c) (tag _ m) _ _ _
    (comp_pat_conf _ _ _ _ cp) vlblr llblr = true ->
  all_cmd_ok_high c m envd cmd1 clblr vlblr
    (fun i' : fin (projT1 envd) =>
      if fin_eq_dec i' i then true else llblr i') Hmatch ->
  all_cmd_ok_high c m envd cmd2 clblr vlblr llblr Hmatch ->
  all_cmd_ok_high c m envd (CompLkup _ envd cp i EQ cmd1 cmd2) clblr vlblr llblr Hmatch.
Proof.
  intros c m envd clblr vlblr llblr cp i EQ
    cmd1 cmd2 Hmatch Hhigh_pat Hhigh_conf Hcmd1 Hcmd2.
  simpl. rewrite Hhigh_pat. unfold hdlr_term in *.
  unfold CT. unfold CTAG. rewrite Hhigh_conf. simpl.
  auto.
Qed.

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
    clear H. destruct KSTD as [n kstd].
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
  (e:expr COMPT COMPS (hdlr_term (CT _ _ c) (CTAG _ m)) envd _) Hmatch,
  vlblr i = false \/
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  cmd_ok_high c m envd (StUpd (hdlr_term (CT _ _ c) (CTAG _ m)) envd i e)
    clblr vlblr llblr Hmatch.
Proof.
  intros c m envd i clblr vlblr llblr e Hmatch H. destruct H as [Hlblr | Hexpr].
    split.
      unfold states_ok, high_out_eq in *. simpl. apply H1.

      unfold states_ok, vars_eq in *; simpl.
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s1) env1 e).
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s2) env2 e).
      simpl in *. clear e. intros.
      destruct s1 as [cs1 tr1 st1].
      destruct s2 as [cs2 tr2 st2].
      clear H. clear H0. destruct KSTD as [n kstd].
      induction n.
        auto.

        destruct kstd. simpl in *. destruct H1.
        destruct i.
        match goal with
        |- context [ if ?e then _ else _ ]
          => destruct e
        end; simpl in *.
        inversion H0. f_equal. destruct st1. destruct st2.
        simpl. apply IHn; auto.
        rewrite <- vlblr_shift; auto.
        
        inversion H0. f_equal. destruct st1. destruct st2.
        simpl. apply IHn; auto.
        rewrite <- vlblr_shift; auto.
        
        unfold fin in *. rewrite Hlblr in *.
        inversion H0. simpl. f_equal. auto.
        
    split.

      unfold states_ok, high_out_eq in *. simpl. apply H1.
      
      unfold vars_eq in *; simpl.
      erewrite hdlr_expr_ok_high_correct
        with (env1:=env1) (env2:=env2); eauto.
      generalize (eval_hdlr_expr PAYD COMPT COMPS KSTD c m
        (kst PAYD COMPT COMPS KSTD s2) env2 e).
      destruct s1; destruct s2. simpl in *. clear Hexpr e.
      simpl. destruct H1 as [Hout Hvars]. clear Hout.
      clear H H0. destruct KSTD as [n kstd]. unfold vars_eq in *.
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
  (e:expr COMPT COMPS (hdlr_term (CT _ _ c) (CTAG _ m)) envd _) Hmatch,
  vlblr i = false \/
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  all_cmd_ok_high c m envd (StUpd (hdlr_term (CT _ _ c) (CTAG _ m)) envd i e)
    clblr vlblr llblr Hmatch.
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

(*Lemma ct_comp_expr : forall c m envd st env ct
  (ce:expr COMPT (hdlr_expr (comp_type _ _ c) (tag _ m)) envd (Comp _ ct)),
  comp_type _ _ 
  
Lemma send_low : forall c m envd clblr vlblr ct
  ce t ple,
  clblr ct = None ->
  cmd_ok_low c m envd (Send _ envd ct ce t ple) clblr vlblr.
Proof.
  intros c m envd clblr vlblr ct ce t ple Hnot_in.
  unfold cmd_ok_low, states_ok. intros.
  split.
    unfold high_out_eq. intros. destruct s as [? [?] ?].
    simpl in *. repeat uninhabit. simpl.
expr COMPT
         (Reflex.hdlr_term PAYD COMPT COMPS KSTD (CT COMPT COMPS c)
            (CTAG PAYD m)) envd (Comp COMPT ct)
(eval_hdlr_expr PAYD COMPT COMPS KSTD c m kst env ce)
    destruct (eval_hdlr_expr PAYD COMPT COMPS KSTD c m kst env ce). auto.

    unfold vars_eq. simpl. auto.
Qed.*)

Lemma send_low_ccomp : forall c m envd clblr vlblr t ple,
  cmd_ok_low c m envd (Send _ envd _
    (Term _ _ _ _ (CComp _ _ _ _ _ _ _)) t ple) clblr vlblr.
Proof.
  intros c m envd clblr vlblr t ple.
  unfold cmd_ok_low, states_ok. intros.
  split.
    unfold high_out_eq. intros. destruct s as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. rewrite H0. auto.

    unfold vars_eq. simpl. auto.
Qed.

Lemma send_high_all : forall c m envd clblr vlblr llblr ct
  ce t ple Hmatch,
  hdlr_expr_ok_high _ _ _ _ ce vlblr llblr = true ->
  pl_expr_ok_high _ _ _ _ _ ple vlblr llblr = true ->
  all_cmd_ok_high c m envd (Send _ envd ct ce t ple) clblr vlblr llblr Hmatch.
Proof.
  simpl. unfold cmd_ok_high. unfold states_ok. simpl.
  intros c m envd clblr vlblr llblr ct ce t ple Hmatch Hexpr
    Hpexpr env1 env2 s1 s2 i ? ? Hstates Hlocals.
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

(*Lemma send_high_all_low_comp : forall c m envd clblr vlblr llblr ct
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
*)

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
  e es i EQ Hmatch,
  all_cmd_ok_high c m envd (Call _ envd e es i EQ) clblr vlblr llblr Hmatch.
Proof.
  intros c m envd clblr vlblr llblr e es i EQ Hmatch.
  simpl. unfold cmd_ok_high. intros.
  unfold states_ok, high_out_eq, vars_eq in *. simpl.
  split.
    intros. destruct s1 as [? [?] ?]; destruct s2 as [? [?] ?].
    simpl in *. repeat uninhabit. simpl. destruct H1. erewrite H1; eauto.

    apply H1.
Qed.

Lemma spawn_high_all : forall c m envd clblr vlblr llblr ct
  ple i EQ Hmatch,
  pl_expr_ok_high _ _ _ _ _ ple vlblr llblr = true ->
  all_cmd_ok_high c m envd (Spawn _ envd ct ple i EQ) clblr vlblr llblr Hmatch.
Proof.
  simpl. unfold cmd_ok_high. unfold states_ok. simpl.
  intros c m envd clblr vlblr llblr ct ple i EQ Hmatch
    Hpexpr env1 env2 s1 s2 f ? ? Hstates Hlocals.
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
  e cmd1 cmd2 Hmatch,
  hdlr_expr_ok_high _ _ _ _ e vlblr llblr = true ->
  all_cmd_ok_high c m envd cmd1 clblr vlblr llblr Hmatch ->
  all_cmd_ok_high c m envd cmd2 clblr vlblr llblr Hmatch ->
  all_cmd_ok_high c m envd (Ite _ envd e cmd1 cmd2) clblr vlblr llblr Hmatch.
Proof.
  intros c m envd clblr vlblr llblr e cmd1 cmd2 Hmatch Hexpr Hcmd1 Hcmd2.
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
    intros. destruct i as [i1 i2]. specialize (Hcmd1 env s i1 H H0).
    destruct Hcmd1 as [Hout1 ?].
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s; hdlr_env := env |} cmd1 i1) as [st env']_eqn.
    assert (ReachInter st) as HRI.
      apply f_equal with (f:=hdlr_kst _ _ _ _ _) in Heqh. simpl in Heqh.
      subst st. eapply ReachInter_run; eauto.
    specialize (Hcmd2 env' st i2 HRI H0). destruct Hcmd2 as [Hout2 ?].
    destruct st as [? [tr''] ?]. simpl in *. rewrite Hout1 with (tr':=tr''); auto.
    apply Hout2 with (tr:=tr'') (tr':=tr'); auto. rewrite <- Heqh. auto.

    unfold cmd_ok_low, vars_eq, ve_st, kstate_run_prog in *. simpl in *.
    destruct i as [i1 i2].
    specialize (Hcmd1 env s i1 H H0). destruct Hcmd1 as [? Hvar1].
    destruct (hdlr_state_run_cmd PAYD COMPT COMPTDEC COMPS KSTD c m envd
                  {| hdlr_kst := s; hdlr_env := env |} cmd1 i1) as [st env']_eqn.
    assert (ReachInter st) as HRI.
      destruct s as [? [?] ?].
      apply f_equal with (f:=hdlr_kst _ _ _ _ _) in Heqh. simpl in Heqh.
      subst st. eapply ReachInter_run; eauto.
    specialize (Hcmd2 env' st i2 HRI H0). destruct Hcmd2 as [? Hvar2].
    rewrite Hvar1. simpl in *. rewrite Heqh. apply Hvar2.
Qed.

Lemma seq_high_all : forall c m envd cmd1 cmd2 clblr vlblr llblr Hmatch,
  all_cmd_ok_high c m envd cmd1 clblr vlblr llblr Hmatch ->
  all_cmd_ok_high c m envd cmd2 clblr vlblr
    (get_llblr (CT _ _ c) (CTAG _ m) envd cmd1 (get_ccomp_cfgp c clblr Hmatch) clblr vlblr llblr) Hmatch ->
  all_cmd_ok_high c m envd (Seq _ _ cmd1 cmd2) clblr vlblr llblr Hmatch.
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
  Reflex.ktr _ _ _ _ s = inhabits tr ->
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
  Reflex.ktr _ _ _ _ s = inhabits tr ->
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

Lemma nop_high : forall clblr vlblr c m envd llblr Hmatch,
  cmd_ok_high c m envd (Nop _ _) clblr vlblr llblr Hmatch.
Proof.
  intros clblr vlblr c m envd llblr.
  unfold cmd_ok_high, states_ok. intros.
  simpl. auto.
Qed.

Lemma nop_high_all : forall clblr vlblr c m envd llblr Hmatch,
  all_cmd_ok_high c m envd (Nop _ _) clblr vlblr llblr Hmatch.
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

Definition low_ok'' clblr vlblr := forall c m,
  lblr_match_comp COMPT COMPTDEC COMPS clblr c = false ->
  cmd_ok_low c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c))) clblr vlblr.

Definition high_ok'' clblr vlblr :=
  forall c m
    (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true),
    cmd_ok_high c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    clblr vlblr (fun _ => true) Hmatch.

Definition high_ok_all clblr vlblr :=
  forall c m
    (Hmatch:lblr_match_comp COMPT COMPTDEC COMPS clblr c = true),
    all_cmd_ok_high c m (projT1 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    (projT2 (HANDLERS (tag PAYD m) (comp_type COMPT COMPS c)))
    clblr vlblr (fun _ => true) Hmatch.

Lemma Reach_ReachInter : forall s,
  Reach PAYD COMPT COMPTDEC COMPS IENVD KSTD INIT HANDLERS s -> ReachInter s.
Proof.
  intros s HReach.
  induction HReach.
    inversion H. subst s0. repeat econstructor.

    inversion H. subst s'0. unfold mk_inter_ve_st.
    repeat econstructor; auto.

    inversion H. unfold mk_bogus_st. repeat econstructor; auto.
Qed.

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
    apply H; auto. unfold mk_inter_ve_st. repeat econstructor; auto. apply Reach_ReachInter; auto.
    apply vars_eq_trans with (s2:=mk_inter_ve_st PAYD COMPT COMPS KSTD c m s tr); auto.
    apply H; auto. unfold mk_inter_ve_st. repeat econstructor; auto. apply Reach_ReachInter; auto.

  unfold high_ok', high_ok'', cmd_ok_high, states_ok, ve_st in *.
  intros. apply H0; auto. 
  unfold mk_inter_ve_st. repeat econstructor; auto. apply Reach_ReachInter; auto.
  unfold mk_inter_ve_st. repeat econstructor; auto. apply Reach_ReachInter; auto.
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