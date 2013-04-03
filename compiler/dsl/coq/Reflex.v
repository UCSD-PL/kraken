Require Import Ascii.
Require Import Bool.
Require Import Eqdep_dec.
Require MSetInterface.
Require Import NPeano.
Require Orders.
Require Import List.
Require Morphisms.
Require Import RelationClasses.
Require Import String.
Require Import Ynot.

Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexTactics.
Require Import ReflexVec.
Require Import ReflexHVec.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.
Open Scope list_scope.

(* Some num/fin/nat stuff *)

Definition num_of_fin {bound : nat} (n : fin bound) := num_of_nat (nat_of_fin n).

Lemma eq_nat_num_of_fin : forall {bound : nat} (f : fin bound) n,
  nat_of_fin f = nat_of_num n -> num_of_fin f = n.
Proof.
  intros ? f n P. pose proof (f_equal num_of_nat P) as P'. rewrite num_nat_embedding in P'.
  exact P'.
Qed.

Inductive desc : Set := num_d | str_d | fd_d.

Definition desc_eqdec : forall x y : desc, decide (x = y).
Proof.
  decide equality.
Qed.

Module DecidableTypeDesc <: DecidableType.
  Definition U := desc.
  Definition eq_dec := desc_eqdec.
End DecidableTypeDesc.

Module DecidableEqDepDesc := DecidableEqDep(DecidableTypeDesc).

Definition UIP_refl_desc :
  forall (d : desc) (e : d = d), e = Logic.eq_refl d :=
  DecidableEqDepDesc.UIP_refl.

Fixpoint sdenote_desc (d : desc) : Set :=
  match d with
  | num_d => num
  | str_d => str
  | fd_d  => fd
  end
.

Instance SDenoted_desc : SDenoted desc :=
{ sdenote := sdenote_desc
}.

Definition vdesc' n : Set := svec desc n.

Definition sdenote_vdesc' n (pt : vdesc' n) : Set :=
  shvec sdenote_desc pt.

Instance SDenoted_vdesc' {n} : SDenoted (vdesc' n) :=
{ sdenote := sdenote_vdesc' n
}.

(* Thank you Ynot for breaking sigT notation... *)
Definition vdesc := (sigT (fun (n : nat) => vdesc' n)).

Definition sdenote_vdesc (v : vdesc) : Set :=
  sdenote_vdesc' (projT1 v) (projT2 v).

Instance SDenoted_vdesc : SDenoted vdesc :=
{ sdenote := sdenote_vdesc
}.

Definition vvdesc n := vec vdesc n.

Section WITH_PAYLOAD_DESC_VEC.

Context {NB_MSG : nat}.
Variable VVD : vvdesc NB_MSG.

Record compd :=
{ compd_name : str
; compd_cmd  : str
; compd_args : list str
; compd_conf : vdesc
}.

Variable COMPT : Set.

Variable COMPTDEC : forall (x y : COMPT), decide (x = y).

Variable COMPS : COMPT -> compd.

Definition lkup_tag (tag : fin NB_MSG) : vdesc :=
  vec_ith VVD tag.

Record msg : Set :=
  { tag : fin NB_MSG
  ; pay : s[[ lkup_tag tag ]]
  }.

Definition trace_recv (f : fd) (d : desc) : s[[ d ]] -> Trace :=
  match d with
  | num_d => fun n : num => RecvNum f n
  | str_d => fun s : str => RecvStr f s
  | fd_d  => fun g : fd  => RecvFD  f g :: nil
  end.

Definition trace_send (f : fd) (d : desc) : s[[ d ]] -> Trace :=
  match d with
  | num_d => fun n : num => SendNum f n
  | str_d => fun s : str => SendStr f s
  | fd_d  => fun g : fd  => SendFD  f g :: nil
  end.

Record bogus_msg : Set :=
  { btag : num
  ; bbad : nat_of_num btag >= NB_MSG
  }.

Definition maybe_msg := (msg + bogus_msg)%type.

Section WITH_TRACE_FUN.

Variable trace_fun : fd -> forall (d : desc), s[[ d ]] -> list Action.

Fixpoint trace_payload' (f : fd) (n : nat) :
  forall (pd : vdesc' n) (p : s[[ pd ]]), Trace :=
  match n with
  | O => fun _ _ => nil
  | S n' => fun pd =>
    let (d, pd') as _pd return forall (p : sdenote_vdesc' (S n') _pd), _ := pd in
    fun p => trace_payload' f n' pd' (snd p) ++ trace_fun f d (fst p)
  end.

Definition trace_payload (pd : vdesc) (f : fd) :=
  trace_payload' f (projT1 pd) (projT2 pd).

Definition trace_opt_payload (opd : option vdesc) (f : fd)
  : s[! opd !] -> Trace :=
  match opd as _opd return s[! _opd !] -> Trace with
  | None => fun p => match p with end
  | Some spt => fun p => trace_payload spt f p
  end.

End WITH_TRACE_FUN.

Definition trace_payload_recv' := trace_payload' trace_recv.

Definition trace_payload_send' := trace_payload' trace_send.

Definition trace_payload_recv := trace_payload trace_recv.

Definition trace_payload_send := trace_payload trace_send.

Definition trace_opt_payload_recv := trace_opt_payload trace_recv.

Definition trace_opt_payload_send := trace_opt_payload trace_send.

Definition trace_recv_msg (f : fd) (m : msg) : Trace :=
  let t := tag m in
  trace_payload_recv (lkup_tag t) f (pay m) ++ RecvNum f (num_of_fin t).

Definition trace_recv_bogus_msg (f : fd) (m : bogus_msg) : Trace :=
  RecvNum f (btag m).

Definition trace_recv_maybe_msg (f : fd) (m : maybe_msg) : Trace :=
  match m with
  | inl m => trace_recv_msg f m
  | inr bm => trace_recv_bogus_msg f bm
  end.

Definition trace_send_msg (f : fd) (m : msg) : Trace :=
  let t := tag m in
  trace_payload_send (lkup_tag t) f (pay m) ++ SendNum f (num_of_fin t).

Definition open_if_fd (t : desc) : s[[ t ]] -> hprop :=
  match t as _t return s[[ _t ]] -> hprop with
  | fd_d => fun v => open v | _ => fun _ => emp
  end.

Definition recv_arg :
  forall (f : fd) (t : desc) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun v : s[[ t ]] => tr ~~
          traced (trace_recv f t v ++ tr) * open f * open_if_fd _ v
        ).
Proof.
  intros; refine (
    match t as _t return STsep _ (fun v : s[[ _t ]] => _) with
    | num_d =>
      n <- recv_num f tr;
      {{ Return n }}
    | str_d =>
      s <- recv_str f tr;
      {{ Return s }}
    | fd_d =>
      g <- recv_fd f tr;
      {{ Return g }}
    end
  );
  sep'.
Qed.

Definition send_arg :
  forall (f : fd) (d : desc) (v : s[[ d ]]) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (trace_send f d v ++ tr) * open f).
Proof.
  intros; refine (
    match d as _d return
      forall v : s[[ _d ]],
      STsep _ (fun _ => tr ~~ traced (trace_send f _d v ++ tr) * _)
    with
    | num_d => fun v =>
      send_num f v tr;;
      {{ Return tt }}
    | str_d => fun v =>
      send_str f v tr;;
      {{ Return tt }}
    | fd_d => fun v =>
      send_fd f v tr;;
      {{ Return tt }}
    end v
  );
  sep'.
Qed.

Fixpoint all_open_payload' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> hprop :=
  match n with
  | 0 => fun _ _ => emp
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> hprop) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      open vd * all_open_payload' n' v' vv'
    | _ => fun vv =>
      let (_, vv') := vv in
      all_open_payload' n' v' vv'
    end
  end.

Definition all_open_payload {v : vdesc} : s[[ v ]] -> hprop :=
  all_open_payload' (projT1 v) (projT2 v).

Definition recv_payload' :
  forall (f : fd) (n : nat) (pd : vdesc' n) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun pv : s[[ pd ]] => tr ~~
          traced (trace_payload_recv' f n pd pv ++ tr) * open f
          * all_open_payload' n pd pv
        ).
Proof.
  intros; refine (
    Fix3
      (fun n pd tr => tr ~~ traced tr * open f)
      (fun n pd tr (pv : s[[ pd ]]) => tr ~~
        traced (trace_payload_recv' f n pd pv ++ tr) * open f
        * all_open_payload' n pd pv)
      (fun self (n : nat) (pd : vdesc' n) tr =>
         match n as _n return
           forall (pd : vdesc' _n), STsep _ (fun x : s[[ pd ]] => _)
         with
         | O => fun _ => {{ Return tt }}
         | S n' => fun pt =>
           match pt with
           | (d, pt') =>
             v  <- recv_arg f d tr;
             vs <- self n' pt' (tr ~~~ trace_recv f d v ++ tr) <@> open_if_fd _ v;
             {{ Return (v, vs) }}
           end
         end pd
      )
    n pd tr
  ); sep'.
  inv H; rewrite app_assoc; sep'.
  destruct d; sep'.
Qed.

Definition recv_payload :
  forall (f : fd) (pd : vdesc) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun pv : s[[ pd ]] => tr ~~
          traced (trace_payload_recv pd f pv ++ tr) * open f
          * all_open_payload pv
        ).
Proof.
  intros f pd. destruct pd as [n pd].
  exact (recv_payload' f n pd).
Qed.

Definition send_payload' :
  forall (f : fd) (n : nat) (pd : vdesc' n) (pv : s[[ pd ]])
         (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit =>
           tr ~~ traced (trace_payload_send' f n pd pv ++ tr) * open f).
Proof.
  intros; refine (
    Fix4
      (fun n pd pv tr => tr ~~ traced tr * open f)
      (fun n pd pv (tr : [Trace]) _ =>
         tr ~~ traced (trace_payload_send' f n pd pv ++ tr) * open f)
      (fun self (n : nat) (pd : vdesc' n) pv (tr : [Trace]) =>
         match n as _n return
           forall (pd : vdesc' _n) (pv : s[[ pd ]]),
             STsep _ (fun _ =>
                        tr ~~ traced (trace_payload_send' f _n pd pv ++ tr) * _)
         with
         | O => fun _ _ => {{ Return tt }}
         | S n' => fun (pd : vdesc' (S n'))
                       (pv : sdenote_vdesc' (S n') pd) =>
           match pd as _pd return
             forall (pv : sdenote_vdesc' (S n') _pd), STsep _ (fun _ => _)
           with
           | (d, pt') => fun pv =>
             match pv with
             | (v, pv') =>
               send_arg f d v tr;;
               self n' pt' pv' (tr ~~~ trace_send f d v ++ tr);;
               {{ Return tt }}
             end
           end pv
         end pd pv
      ) n pd pv tr);
  sep';
  try rewrite app_assoc; sep'.
Qed.

Definition send_payload :
  forall (f : fd) (pd : vdesc) (pv : s[[ pd ]]) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (trace_payload_send pd f pv ++ tr) * open f).
Proof.
  intros f pd. destruct pd as [n pd].
  exact (send_payload' f n pd).
Qed.

Definition recv_msg :
  forall (f : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun m : maybe_msg => tr ~~
          traced (trace_recv_maybe_msg f m ++ tr) * open f
          * match m with inl msg => all_open_payload (pay msg) | inr bog => emp end
        ).
Proof.
  intros; refine (
    t <- recv_num f tr;
    let oft := opt_fin NB_MSG (nat_of_num t) in
    match oft with
    | inleft (existT ft pf) =>
      let pt := lkup_tag ft in
      pv <- recv_payload f pt (tr ~~~ RecvNum f t ++ tr);
      {{ Return (inl _ (Build_msg ft pv)) }}
    | inright pf => {{ Return (inr _ (Build_bogus_msg t pf)) }}
    end
  ); sep'; try discriminate;
  match goal with
  | [H: ?inx _ _ = ?inx _ _ |- _] => inv H
  end.
  unfold trace_recv_msg, pt. simpl. rewrite (eq_nat_num_of_fin ft t pf), app_assoc. sep'.
  unfold trace_recv_msg, pt. simpl. rewrite (eq_nat_num_of_fin ft t pf), app_assoc. sep'.
  unfold trace_recv_bogus_msg. sep'.
  unfold trace_recv_bogus_msg. sep'.
Qed.

Definition send_msg :
  forall (f : fd) (m : msg) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (trace_send_msg f m ++ tr) * open f).
Proof.
  intros; refine (
    let t := tag m in
    let pt := lkup_tag t in
    send_num f (num_of_fin t) tr;;
    send_payload f pt (pay m) (tr ~~~ SendNum f (num_of_fin t) ++ tr);;
    {{ Return tt }}
  );
  sep'.
  unfold trace_send_msg, pt, t. clear t pt. destruct m as [t p]. simpl in *.
  rewrite app_assoc; sep'.
Qed.

Inductive KAction : Set :=
| KExec   : str -> list str -> fd -> KAction
| KCall   : str -> list str -> fd -> KAction
| KSelect : list fd -> fd -> KAction
| KSend   : fd -> msg -> KAction
| KRecv   : fd -> msg -> KAction
| KBogus  : fd -> bogus_msg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args f => Exec cmd args f :: nil
  | KCall cmd args pipe => Call cmd args pipe :: nil
  | KSelect cs f => Select cs f :: nil
  | KSend f m => trace_send_msg f m
  | KRecv f m => trace_recv_msg f m
  | KBogus f bm => trace_recv_bogus_msg f bm
  end.

Fixpoint expand_ktrace (kt : KTrace) : Trace :=
  match kt with
  | nil => nil
  | ka :: kas => expand_kaction ka ++ expand_ktrace kas
  end.

Variable KSTD : vdesc.
Notation KSTD_SIZE := (projT1 KSTD).
Notation KSTD_DESC := (projT2 KSTD).

Definition comp_conf_desc compt := compd_conf (COMPS compt).

Record comp : Set :=
{ comp_type : COMPT
; comp_fd   : fd
; comp_conf : s[[ comp_conf_desc comp_type ]]
}.

Definition sdenote_desc_cfg_pat (d:desc) : Set := option (sdenote_desc d).

Record comp_pat : Set :=
{ comp_pat_type : COMPT
; comp_pat_fd   : option fd
; comp_pat_conf : shvec sdenote_desc_cfg_pat (projT2 (comp_conf_desc comp_pat_type))
}.

Definition elt_match (d:desc) (elt:s[[d]]) (elt':sdenote_desc_cfg_pat d) : bool :=
  match elt' with
  | None   => true
  | Some x =>
    match d as _d return s[[_d]] -> s[[_d]] -> bool with
    | num_d => fun elt x => if num_eq x elt then true else false
    | str_d => fun elt x => if str_eq x elt then true else false
    | fd_d  => fun elt x => if fd_eq x elt then true else false
    end elt x
  end.

Definition match_comp (cp : comp_pat) (c : comp) : bool :=
  match c, cp with
  | Build_comp t f cfg, Build_comp_pat t' fp cfgp =>
    match COMPTDEC t t' with
    | left EQ =>
      match fp with None => true | Some f' => if fd_eq f f' then true else false end
      &&
      match EQ in _ = _t return
        shvec sdenote_desc_cfg_pat (projT2 (comp_conf_desc _t)) -> bool
      with
      | Logic.eq_refl => fun cfgp =>
        shvec_match (projT2 (comp_conf_desc t))
                    sdenote_desc sdenote_desc_cfg_pat
                    elt_match cfg cfgp
      end cfgp
    | right _ => false
    end
  end.

Definition find_comp (cp : comp_pat) (comps : list comp) :=
  find (match_comp cp) comps.

Definition filter_comps (cp : comp_pat) (comps : list comp) :=
  filter (match_comp cp) comps.

Definition exists_comp (cp : comp_pat) (comps : list comp) :=
  match find_comp cp comps with
  | None   => false
  | Some _ => true
  end.

Record kstate : Type := mkst
  { kcs : list comp
  ; ktr : [KTrace]
  ; kst : s[[ KSTD ]]
  ; kfd : FdSet.t (* need to keep track of all the open fds... *)
  }.

Inductive unop : desc -> desc -> Set :=
| Not : unop num_d num_d
.

Definition eval_unop
  (d1 d2 : desc) (op : unop d1 d2) (v : s[[ d1 ]]) : s[[ d2 ]] :=
  match op in unop t1 t2 return s[[ t1 ]] -> s[[ t2 ]] with
  | Not => fun v => if num_eq v FALSE then TRUE else FALSE
  end v.

Implicit Arguments eval_unop.

Inductive binop : desc -> desc -> desc -> Set :=
| Eq  : forall t, binop t t num_d
| Add : binop num_d num_d num_d
| Sub : binop num_d num_d num_d
| Mul : binop num_d num_d num_d
| Cat : binop str_d str_d str_d
.

Definition eval_binop
  (d1 d2 d3: desc) (op : binop d1 d2 d3) (v1 : s[[ d1 ]]) (v2 : s[[ d2 ]]) : s[[ d3 ]] :=
  match op in binop _d1 _d2 _d3 return s[[ _d1 ]] -> s[[ _d2 ]] -> s[[ _d3 ]] with
  | Eq d => fun v1 v2 : s[[ d ]] =>
    let teq : forall (x y : s[[ d ]]), {x = y} + {x <> y} :=
      match d with
      | num_d => num_eq
      | str_d => str_eq
      | fd_d  => fd_eq
      end
    in
    if teq v1 v2 then TRUE else FALSE
  | Add => fun v1 v2 : num =>
    num_of_nat (plus (nat_of_num v1) (nat_of_num v2))
  | Sub => fun v1 v2 : num =>
    num_of_nat (minus (nat_of_num v1) (nat_of_num v2))
  | Mul => fun v1 v2 : num =>
    num_of_nat (mult (nat_of_num v1) (nat_of_num v2))
  | Cat => fun v1 v2 : str =>
    v1 ++ v2
  end v1 v2.

Implicit Arguments eval_binop.

Section WITHIN_HANDLER.

Variable CKST : kstate.
Variable CFD : fd.
Variable CMSG : msg.

Definition CPAY : vdesc := lkup_tag (tag CMSG).

Definition msg_param_i (i : fin (projT1 CPAY)) : s[[ svec_ith (projT2 CPAY) i ]] :=
  shvec_ith _ (projT2 CPAY) (pay CMSG) i.

Fixpoint all_open_payload_drop' (n : nat) :
  forall (v : vdesc' n) (drop : fd), sdenote_vdesc' n v -> hprop :=
  match n with
  | 0 => fun _ _ _ => emp
  | S n' => fun v drop =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> hprop) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      if fd_eq vd drop
      then all_open_payload' n' v' vv'
      else open vd * all_open_payload_drop' n' v' drop vv'
    | _ => fun vv =>
      let (_, vv') := vv in
      all_open_payload_drop' n' v' drop vv'
    end
  end.

Definition all_open_payload_drop {v : vdesc} : fd -> s[[ v ]] -> hprop :=
  all_open_payload_drop' (projT1 v) (projT2 v).

Definition fd_in_payload' := shvec_in sdenote_desc desc_eqdec fd_d.
Definition fd_in_payload f (vd : vdesc) p := fd_in_payload' f (projT1 vd) (projT2 vd) p.

Lemma unpack_all_open_payload' :
  forall (n : nat) (vd : vdesc' n) (p : s[[ vd ]]) (f : fd),
  fd_in_payload' f n vd p ->
  all_open_payload' n vd p ==> open f * all_open_payload_drop' n vd f p.
Proof.
  intros n vd p f IN. induction n.
  contradiction.
  simpl in vd. destruct vd as [d vd'].
  simpl in p. destruct p as [v p'].
  simpl in IN. destruct (desc_eqdec fd_d d).
  simpl in *. destruct e. intuition.
  subst. destruct (fd_eq f f); sep fail idtac.
  destruct (fd_eq v f); sep fail idtac.
  specialize (IHn _ _ H). eapply himp_trans. apply IHn. sep fail idtac.
  simpl. destruct d; first [ exact (IHn _ _ IN) | congruence ].
Qed.

Lemma unpack_all_open_payload :
  forall (vd : vdesc) (p : s[[ vd ]]) (f : fd),
  fd_in_payload f vd p ->
  all_open_payload p ==> open f * all_open_payload_drop f p.
Proof.
  intros vd p f IN.
  pose proof (unpack_all_open_payload' (projT1 vd) (projT2 vd) p f IN).
  exact H.
Qed.

Lemma repack_all_open_payload' :
  forall (n : nat) (vd : vdesc' n) (p : s[[ vd ]]) (f : fd),
  fd_in_payload' f n vd p ->
  open f * all_open_payload_drop' n vd f p ==> all_open_payload' n vd p.
Proof.
  intros n vd p f IN. induction n.
  contradiction.
  simpl in vd. destruct vd as [d vd'].
  simpl in p. destruct p as [v p'].
  simpl in IN. destruct (desc_eqdec fd_d d).
  simpl in *. destruct e. intuition.
  subst. destruct (fd_eq f f); sep fail idtac.
  destruct (fd_eq v f); sep fail idtac.
  specialize (IHn _ _ H). eapply himp_trans; [ | apply IHn]. sep fail idtac.
  simpl. destruct d; first [ exact (IHn _ _ IN) | congruence ].
Qed.

Lemma repack_all_open_payload :
  forall (vd : vdesc) (p : s[[ vd ]]) (f : fd),
  fd_in_payload f vd p ->
  open f * all_open_payload_drop f p ==> all_open_payload p.
Proof.
  intros vd p f IN.
  pose proof (repack_all_open_payload' (projT1 vd) (projT2 vd) p f IN).
  exact H.
Qed.

Definition env_fds_in l (envd : vdesc) (env : s[[ envd ]]) : Prop :=
  forall i,
  match svec_ith (projT2 envd) i as _d return s[[ _d ]] -> Prop with
  | fd_d => fun (f : s[[ fd_d ]]) => In f l
  | _ => fun _ => True
  end (shvec_ith _ (projT2 envd) env i).

Definition proj_fds : list comp -> list fd :=
  map (fun comp => comp_fd comp).

Definition msg_fds_ok : Prop :=
  forall i,
  let d := svec_ith (projT2 CPAY) i in
  match d as _d return s[[ _d ]] -> Prop with
  | fd_d => fun (f : s[[ fd_d ]]) => In f (proj_fds (kcs CKST))
  | _ => fun _ => True
  end (msg_param_i i).

Definition msg_fds_ck : decide msg_fds_ok.
Proof.
  apply forall_fin. intros i. generalize (msg_param_i i).
  destruct (svec_ith (projT2 CPAY) i).
  now left. now left.
  intros s. destruct CKST as [comps ktr]. simpl in *. apply in_dec. exact fd_eq.
Qed.

Section WITH_ENVD.

Variable ENVD : vdesc.
Notation ENVD_SIZE := (projT1 ENVD).
Notation ENVD_DESC := (projT2 ENVD).

Inductive base_term : desc -> Set :=
| SLit  : str -> base_term str_d
| NLit  : num -> base_term num_d
| Var   : forall (i : fin ENVD_SIZE), base_term (svec_ith ENVD_DESC i)
.

Inductive hdlr_term : desc -> Set :=
| Base  : forall {d}, base_term d -> hdlr_term d
| CFd   : hdlr_term fd_d
| MVar  : forall (i : fin (projT1 CPAY)), hdlr_term (svec_ith (projT2 CPAY) i)
| StVar : forall (i : fin KSTD_SIZE), hdlr_term (svec_ith KSTD_DESC i)
.

Section WITH_TERM.

Variable TERM : desc -> Set.

Inductive expr : desc -> Set :=
| Term  : forall {d}, TERM d -> expr d
| UnOp  : forall {d1 d2}, unop d1 d2 -> expr d1 -> expr d2
| BinOp : forall {d1 d2 d3}, binop d1 d2 d3 -> expr d1 -> expr d2 -> expr d3
.

Fixpoint payload_expr' (n : nat) (pd : vdesc' n) : Type :=
  match n as _n return vdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vdesc' (S n')) =>
    match pd with
    | (d, pd') => expr d * payload_expr' n' pd'
    end
  end%type pd.

Definition payload_expr pd := payload_expr' (projT1 pd) (projT2 pd).

Section WITH_PROG_ENV.

Variable ENV : s[[ ENVD ]].
Variable KST : s[[ KSTD ]].

Definition eval_base_term {d} (t : base_term d) : s[[ d ]] :=
  match t with
  | SLit s  => s
  | NLit n  => n
  | Var i   => shvec_ith _ (projT2 ENVD) ENV i
  end.

Definition eval_hdlr_term {d} (t : hdlr_term d) : s[[ d ]] :=
  match t with
  | Base _ bt => eval_base_term bt
  | CFd       => CFD
  | MVar i    => shvec_ith _ (projT2 CPAY) (pay CMSG) i
  | StVar i   => shvec_ith _ (projT2 KSTD) KST i
  end.

Variable EVAL_TERM : forall (d : desc), TERM d -> s[[ d ]].

Fixpoint eval_expr {d} (e : expr d) : s[[ d ]] :=
  match e with
  | Term _ t => EVAL_TERM _ t
  | UnOp _ _ op e =>
    let v := eval_expr e in
    eval_unop op v
  | BinOp _ _ _ op e1 e2 =>
    let v1 := eval_expr e1 in
    let v2 := eval_expr e2 in
    eval_binop op v1 v2
  end.

Fixpoint eval_payload_expr' (n : nat) :
  forall (pd : vdesc' n), payload_expr' n pd -> s[[ pd ]] :=
  let res n pd := payload_expr' n pd -> s[[ pd ]] in
  match n as _n return
    forall (pd : vdesc' _n), res _n pd
  with
  | O => fun _ _ => tt
  | S n' => fun pd =>
    let (d, pd') as _pd return res (S n') _pd := pd in
    fun e =>
      let (v, e') := e in
      (eval_expr v, eval_payload_expr' n' pd' e')
  end.

Definition eval_payload_expr (pd : vdesc) (e : payload_expr pd) : s[[ pd ]] :=
  eval_payload_expr' (projT1 pd) (projT2 pd) e.

Inductive cmd : Type :=
| Send  : expr fd_d -> forall (t : fin NB_MSG), payload_expr (lkup_tag t) -> cmd
| Spawn :
    forall (t : COMPT), s[[ comp_conf_desc t ]] ->
    forall (i : fin ENVD_SIZE), svec_ith ENVD_DESC i = fd_d -> cmd
| StUpd : forall i, expr (svec_ith (projT2 KSTD) i) -> cmd
.

Record init_state :=
{ init_comps : list comp
; init_ktr   : [KTrace]%type
; init_env   : s[[ ENVD ]]
; init_kst   : s[[ KSTD ]]
; init_fds   : FdSet.t
}.

End WITH_PROG_ENV.

End WITH_TERM.

Definition init_cmd := init_state -> cmd base_term.

Definition init_prog := list init_cmd.

Definition hdlr_cmd := kstate -> cmd hdlr_term.

Definition hdlr_prog := kstate -> list hdlr_cmd.

Definition cmd_input_desc {t} (c : cmd t)  :=
  match c with
  | Send _ _ _  => None
  | Spawn _ _ _ _ => Some fd_d
  | StUpd _ _ => None
  end.

Definition sdenote_option {T : Type} (sdenote_content : T -> Set) (o : option T) : Set :=
  match o with
  | Some x => sdenote_content x
  | None => unit
  end.

Definition cmd_input {t} (c : cmd t) : Set :=
  sdenote_option sdenote_desc (cmd_input_desc c).

Definition shvec_replace_cast {d} {i : fin ENVD_SIZE} (EQ : svec_ith ENVD_DESC i = d) e v
  :=
  shvec_replace_ith sdenote_desc _ e i
    (match EQ in _ = _d return s[[ _d ]] -> _ with Logic.eq_refl => fun x => x end v).

Definition eval_base_expr {d} (e : s[[ENVD]]) : expr base_term d -> s[[ d ]] :=
  eval_expr base_term (@eval_base_term e).

Definition eval_base_payload_expr e :=
  eval_payload_expr base_term (@eval_base_term e).

Definition eval_hdlr_expr {d} (e : s[[ENVD]]) (s : s[[KSTD]]) : expr hdlr_term d -> s[[ d ]] :=
  eval_expr hdlr_term (@eval_hdlr_term e s).

Definition eval_hdlr_payload_expr e s :=
  eval_payload_expr hdlr_term (@eval_hdlr_term s e).

Definition init_state_run_cmd (s : init_state) (cmd : cmd base_term)
  : cmd_input cmd -> init_state :=
  let (cs, tr, e, st, fds) := s in
  match cmd as _cmd return cmd_input _cmd -> init_state with

  | Send fe t me => fun _ =>
    let f := eval_base_expr e fe in
    let m := eval_base_payload_expr e _ me in
    {| init_comps := cs
     ; init_ktr   := tr ~~~ KSend f (Build_msg t m) :: tr
     ; init_env   := e
     ; init_kst   := st
     ; init_fds   := fds
     |}

  | Spawn ct cfg i EQ => fun (c:fd) =>
    let comp := COMPS ct in
    {| init_comps := {| comp_type := ct; comp_fd := c; comp_conf := cfg |} :: cs
     ; init_ktr   := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
     ; init_env   := shvec_replace_cast EQ e c
     ; init_kst   := st
     ; init_fds   := FdSet.add c fds
     |}

  | StUpd i ve => fun _ =>
    let v := eval_base_expr e ve in
    {| init_comps := cs
     ; init_ktr   := tr
     ; init_env   := e
     ; init_kst   := shvec_replace_ith _ _ st i v
     ; init_fds   := fds
     |}
  end.

Fixpoint init_state_run_prog_return_type s p :=
  match p with
  | c :: cs =>
    sigT (fun (x : cmd_input (c s)) =>
            init_state_run_prog_return_type (init_state_run_cmd s (c s) x) cs)
  | nil => unit
  end.

Fixpoint init_state_run_prog (s : init_state) (p : init_prog) :
  init_state_run_prog_return_type s p -> init_state
  :=
  match p as _p return init_state_run_prog_return_type s _p -> init_state with
  | c :: cs => fun v =>
    match v with
    | existT x rest =>
      init_state_run_prog (init_state_run_cmd s (c s) x) cs rest
    end
  | nil => fun _ => s
  end.

Record hdlr_state :=
{ hdlr_kst : kstate
; hdlr_env : s[[ ENVD ]]
}.

(* This should probably move out once the environment can change *)
Definition hdlr_state_run_cmd (s : hdlr_state) (cmd : cmd hdlr_term)
  : cmd_input cmd -> hdlr_state :=
  let (s', env) := s in
  let (cs, tr, st, fd) := s' in
  match cmd as _cmd return cmd_input _cmd -> _ with

  | Send fe t me => fun _ =>
    let f := eval_hdlr_expr env st fe in
    let m := eval_hdlr_payload_expr st env _ me in
    {| hdlr_kst :=
         {| kcs := cs
          ; ktr := tr ~~~ KSend f (Build_msg t m) :: tr
          ; kst := st
          ; kfd := fd
          |}
     ; hdlr_env := env
    |}

  | Spawn ct cfg i EQ => fun c =>
    let comp := COMPS ct in
    {| hdlr_kst :=
         {| kcs := {| comp_type := ct; comp_fd := c; comp_conf := cfg |} :: cs
          ; ktr := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
          ; kst := st
          ; kfd := FdSet.add c fd
          |}
     ; hdlr_env := shvec_replace_cast EQ env c
     |}

  | StUpd i ve => fun _ =>
    let v := eval_hdlr_expr env st ve in
    {| hdlr_kst :=
         {| kcs := cs
          ; ktr := tr
          ; kst := shvec_replace_ith _ _ st i v
          ; kfd := fd
          |}
     ; hdlr_env := env
     |}
  end.

Fixpoint hdlr_state_run_prog_return_type s p :=
  match p with
  | c :: cs =>
    sigT (fun (x : cmd_input (c (hdlr_kst s))) =>
            hdlr_state_run_prog_return_type (hdlr_state_run_cmd s (c (hdlr_kst s)) x) cs)
  | nil => unit
  end.

Fixpoint hdlr_state_run_prog (s : hdlr_state) (p : list hdlr_cmd) :
  hdlr_state_run_prog_return_type s p -> hdlr_state
  :=
  match p as _p return hdlr_state_run_prog_return_type s _p -> hdlr_state with
  | c :: cs => fun v =>
    match v with
    | existT x rest =>
      hdlr_state_run_prog (hdlr_state_run_cmd s (c (hdlr_kst s)) x) cs rest
    end
  | nil => fun _ => s
  end.

Definition devnull := Num "000" "000".

Axiom devnull_open : emp ==> open devnull.

Fixpoint default_payload' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v :=
  match n with
  | O    => fun _ => tt
  | S n' => fun v =>
    match v with
    | (d, v') =>
      ( match d as _d return sdenote_desc _d with
        | num_d => FALSE
        | str_d => nil
        | fd_f  => devnull
        end
      , default_payload' n' v')
    end
  end.

Definition default_payload (v : vdesc) : s[[ v ]] :=
  default_payload' (projT1 v) (projT2 v).

Definition default_hdlr_state s :=
  {| hdlr_kst := s; hdlr_env := default_payload ENVD |}.

Definition kstate_run_prog_return_type s p :=
  hdlr_state_run_prog_return_type (default_hdlr_state s) p.

Definition kstate_run_prog (s : kstate) (p : hdlr_prog)
  (input : kstate_run_prog_return_type s (p s))
  : kstate :=
  hdlr_kst (hdlr_state_run_prog (default_hdlr_state s) (p s) input).

Lemma eval_base_expr_fd :
  forall (l : list fd) (d : desc) (v : s[[d]]) (env : s[[ENVD]]) e,
  env_fds_in l ENVD env ->
  eval_base_expr env e = v ->
  match d as _d return (s[[ _d ]] -> Prop) with
  | fd_d => fun f => In f l
  | _ => fun _ => True
  end v.
Proof.
  induction e; try tauto; intros OKE E; simpl in *.
  destruct t; try tauto.
  subst. exact (OKE i).
  now destruct u.
  now destruct b.
Qed.

Lemma eval_hdlr_expr_fd :
  forall (l : list fd) d (env : s[[ENVD]]) (st : s[[KSTD]]) (v : s[[d]]) e,
  In CFD l ->
  env_fds_in l _ env ->
  env_fds_in l _ st ->
  env_fds_in l _ (pay CMSG) ->
  eval_hdlr_expr env st e = v ->
  match d as _d return (s[[ _d ]] -> Prop) with
  | fd_d => fun f => In f l
  | _ => fun _ => True
  end v.
Proof.
  induction e; try tauto; intros IN OKE OKS OKM E; simpl in *.
  destruct t; try tauto; simpl in *.
  destruct b; try tauto.
  subst. exact (OKE i).
  now subst.
  subst. exact (OKM i).
  subst. exact (OKS i).
  now destruct u.
  now destruct b.
Qed.

End WITH_ENVD.

End WITHIN_HANDLER.

Variable IENVD : vdesc.

Variable IPROG : init_prog IENVD.

Definition initial_init_state :=
  {| init_comps := nil
   ; init_ktr   := [nil]%inhabited
   ; init_env   := default_payload IENVD
   ; init_kst   := default_payload KSTD
   ; init_fds   := FdSet.singleton devnull
   |}.

Section WITH_HANDLER.

Definition handlers := forall (m : msg) (cfd : fd),
  sigT (fun (prog_envd : vdesc) => hdlr_prog m prog_envd).

Variable HANDLERS : handlers.

Fixpoint payload_fds_set' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> FdSet.t :=
  match n with
  | 0 => fun _ _ => FdSet.empty
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> FdSet.t) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      FdSet.add vd (payload_fds_set' n' v' vv')
    | _ => fun vv =>
      let (_, vv') := vv in
      payload_fds_set' n' v' vv'
    end
  end.

Definition payload_fds_set (v : vdesc) : s[[ v ]] -> FdSet.t :=
  payload_fds_set' (projT1 v) (projT2 v).


Fixpoint payload_fds' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> list fd :=
  match n with
  | 0 => fun _ _ => nil
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> list fd) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      vd :: payload_fds' n' v' vv'
    | _ => fun vv =>
      let (_, vv') := vv in
      payload_fds' n' v' vv'
    end
  end.

Definition payload_fds (v : vdesc) : s[[ v ]] -> list fd :=
  payload_fds' (projT1 v) (projT2 v).

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall s input,
  s = init_state_run_prog IENVD initial_init_state IPROG input ->
  Reach {| kcs := init_comps _ s
         ; ktr := init_ktr _ s
         ; kst := init_kst _ s
         ; kfd := FdSet.union
                    (payload_fds_set _ (init_kst _ s))
                    (payload_fds_set _ (init_env _ s))
         |}
| Reach_valid :
  forall s f m tr s' input,
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  s' = {| kcs := cs
        ; ktr := [KRecv f m :: KSelect (proj_fds cs) f :: tr]
        ; kst := kst s
        ; kfd := FdSet.union (payload_fds_set _ (pay m)) (kfd s)
        |} ->
  Reach (kstate_run_prog f m (projT1 (HANDLERS m f)) s' (projT2 (HANDLERS m f)) input)
| Reach_bogus :
  forall s s' f bmsg tr,
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  (* introducing s' makes it easier to eapply Reach_bogus *)
  s' = {| kcs := cs
        ; ktr := [KBogus f bmsg :: KSelect (proj_fds cs) f :: tr]
        ; kst := kst s
        ; kfd := kfd s
        |} ->
  Reach s'
.

Definition all_open_set s := all_open (FdSet.elements s).

Definition all_open_set_drop f s := all_open (FdSet.elements (FdSet.remove f s)).

Definition all_fds_in l s := List.Forall (fun x => FdSet.In (comp_fd x) s) l.

Definition pl_fds_subset {envd} (env : s[[envd]]) (s : FdSet.t) :=
  FdSet.Subset (payload_fds_set envd env) s.

Definition init_invariant {envd} (s : init_state envd) :=
  let fds := init_fds _ s in
  all_open_set fds
  * [all_fds_in (init_comps _ s) fds]
  * [pl_fds_subset (init_env _ s) fds]
.

Definition hdlr_invariant {envd} (cfd : fd) (cm : msg) (s : hdlr_state envd) :=
  let (kst, env) := s in
  let fds := kfd kst in
  all_open_set fds
  * [FdSet.In cfd fds]
  * [all_fds_in (kcs kst) fds]
  * [pl_fds_subset env fds]
  * [pl_fds_subset (pay cm) fds]
.

Definition kstate_inv s : hprop :=
  let fds := kfd s in
  tr :~~ ktr s in
  traced (expand_ktrace tr)
  * all_open_set fds
  * [Reach s]
  * [all_fds_in (kcs s) fds]
  * [pl_fds_subset (kst s) fds]
  .

Definition open_payload_frame_base {ENVD d}
  (s : FdSet.t) (*env : s[[ ENVD ]]*) (bt : base_term ENVD d) (f : s[[ d ]])
  : hprop
  :=
  match bt in base_term _ _d return s[[ _d ]] -> hprop with
  | SLit s => fun _ => emp
  | NLit n => fun _ => emp
  | Var i => fun f =>
    match svec_ith (projT2 ENVD) i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => all_open_set_drop f s (*all_open_payload_drop f env*)
    end f
  end f.

Definition open_payload_frame_hdlr {CMSG ENVD d}
  (cfd : fd) (s : FdSet.t) (ht : hdlr_term CMSG ENVD d) (f : s[[ d ]])
  : hprop
  :=
  match ht in hdlr_term _ _ _d return s[[ _d ]] -> hprop with
  | Base _ bt => fun f => open_payload_frame_base s bt f
  | CFd => fun _ => all_open_set_drop cfd s
  | MVar i => fun f =>
    match svec_ith (projT2 (lkup_tag (tag CMSG))) i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => all_open_set_drop f s
    end f
  | StVar i => fun f =>
    match svec_ith KSTD_DESC i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => all_open_set_drop f s
    end f
  end f.

(*
Definition open_payload_frame_hdlr {CMSG ENVD d}
  (cfd : fd) (env : s[[ ENVD ]]) (st : s[[ KSTD ]])
  (ht : hdlr_term CMSG ENVD d) (f : s[[ d ]])
  : hprop
  :=
  match ht in hdlr_term _ _ _d return s[[ _d ]] -> hprop with
  | Base _ bt => fun f => open_payload_frame_base env bt f
  | CFd => fun _ => all_open_payload env * all_open_payload st
  | MVar i => fun f =>
    match svec_ith (projT2 (lkup_tag (tag CMSG))) i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => open cfd * all_open_payload env * all_open_payload_drop f st
    end f
  | StVar i => fun f =>
    match svec_ith KSTD_DESC i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => open cfd * all_open_payload env * all_open_payload_drop f st
    end f
  end f.
*)

Definition open_payload_frame_expr {term : desc -> Set} {d}
  (opft : term d -> s[[d]] -> hprop) (e : expr term d) (f : s[[d]])
  : hprop
  :=
  match e in expr _ _d return (term _d -> s[[_d]] -> hprop) -> s[[_d]] -> hprop with
  | Term _ t => fun opft f => opft t f
  | UnOp _ _ op e1 => fun _ _ => emp
  | BinOp _ _ _ op e1 e2 => fun _ _ => emp
  end opft f.

Definition open_payload_frame_base_expr' {ENVD d} (s : FdSet.t)
  : expr (base_term ENVD) d -> s[[d]] -> hprop
  := open_payload_frame_expr (open_payload_frame_base s)
.

Definition open_payload_frame_base_expr {ENVD d}
  (e : s[[ENVD]]) cs (fds : FdSet.t) (exp : expr (base_term ENVD) d) (res : s[[d]]) : hprop
  :=
  open_payload_frame_base_expr' fds exp res
  * [all_fds_in cs fds]
  * [pl_fds_subset e fds]
.

Definition open_payload_frame_hdlr_expr' {CMSG ENVD d} (cfd : fd) (s : FdSet.t)
  : expr (hdlr_term CMSG ENVD) d -> s[[d]] -> hprop
  := open_payload_frame_expr (open_payload_frame_hdlr cfd s).

Definition open_payload_frame_hdlr_expr {CMSG ENVD d}
  (e : s[[ENVD]]) cs cm (cfd : fd) (fds : FdSet.t) (exp : expr (hdlr_term CMSG ENVD) d)
  (res : s[[d]]) : hprop
  :=
  open_payload_frame_hdlr_expr' cfd fds exp res
  * [FdSet.In cfd fds]
  * [all_fds_in cs fds]
  * [pl_fds_subset e fds]
  * [pl_fds_subset (pay cm) fds]
.

Ltac isolate t :=
  match t with ?lhs ==> ?rhs =>
    refine (@himp_trans (lhs * _) _ _ _ _); [ sep' | ];
    refine (@himp_trans (rhs * _) _ _ _ _); [ | sep' ];
    apply himp_split
  end.

Ltac opens_packing :=
  match goal with
  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_open_drop ?cs ?c ] =>
      isolate (open c * all_open_drop cs c ==> all_open cs);
      [ apply repack_all_open | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match rhs with context [ all_open_drop ?cs ?c ] =>
      isolate (all_open cs ==> open c * all_open_drop cs c);
      [ apply unpack_all_open | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_open_drop ?cs ?c ] =>
    match rhs with context [ all_open_drop ?cs ?d ] =>
      isolate (open c * all_open_drop cs c ==> open d * all_open_drop cs d);
      [ eapply himp_trans; [ apply repack_all_open | apply unpack_all_open ] | ]
    end
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_open_payload_drop ?f ?p ] =>
      isolate (open f * all_open_payload_drop f p ==> all_open_payload p);
      [ apply repack_all_open_payload | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match rhs with context [ all_open_payload_drop ?f ?p ] =>
      isolate (all_open_payload p ==> open f * all_open_payload_drop f p);
      [ apply unpack_all_open_payload | ]
    end

  | [ |- ?lhs ==> ?rhs ] =>
    match lhs with context [ all_open_payload_drop ?f ?p ] =>
    match rhs with context [ all_open_payload_drop ?g ?p ] =>
      isolate (open f * all_open_payload_drop f p ==> open g * all_open_drop g p);
      [ eapply himp_trans;
        [ apply repack_all_open_payload | apply unpack_all_open_payload ] | ]
    end
    end
end.

Ltac uninhabit :=
  match goal with
  | [ H1: ?tr = [_]%inhabited, H2: context[inhabit_unpack ?tr _] |- _ ] =>
    rewrite H1 in H2; simpl in H2
  | [ H: ?tr = [_]%inhabited |- context[inhabit_unpack ?tr _] ] =>
    rewrite H; simpl
  | [ H: ktr ?s = [_]%inhabited |- _ ] =>
    unfold s in *; simpl in *
  | [ H1 : ktr ?s = [_]%inhabited, H2 : ktr ?s = [_]%inhabited |- _ ] =>
    rewrite H1 in H2; apply pack_injective in H2;
    rewrite -> H2 in * || rewrite <- H2 in * (* subst may be blocked *)
  | [ H : [?x]%inhabited = [?y]%inhabited |- _ ] =>
    apply pack_injective in H; try first [subst x | subst y]
  end.

Ltac misc :=
  match goal with
  | [ |- Reach _ ] => solve [econstructor; eauto]
  end.

Ltac unfoldr :=
  unfold kstate_inv, init_invariant, hdlr_invariant,
  open_payload_frame_base_expr, open_payload_frame_hdlr_expr.

Ltac simplr :=
  try uninhabit;
  discharge_pure;
  try opens_packing;
  try misc.

Ltac sep'' :=
  sep unfoldr simplr.

Theorem numd_neq_fdd : num_d = fd_d -> False. Proof. discriminate. Qed.
Theorem strd_neq_fdd : str_d = fd_d -> False. Proof. discriminate. Qed.

Theorem all_open_payload_replace' :
  forall (ds : nat) (d : vdesc' ds) (st : sdenote_vdesc' ds d) i v
         (H : svec_ith d i = fd_d -> False),
  all_open_payload' _ _ st ==>
  all_open_payload' _ _ (shvec_replace_ith sdenote_desc d st i v).
Proof.
  intros. induction ds.
  destruct i.
  simpl in d, i, st.
  destruct d as [d d']. destruct i as [i'|]. destruct st as [st st'].
  specialize (IHds d' st' i' v H).
  simpl. destruct d; sep''.
  simpl in *. destruct d, st; simpl in *; sep''.
Qed.

Theorem all_open_payload_replace :
  forall (d : vdesc) (st : sdenote_vdesc d) i v (H : svec_ith (projT2 d) i = fd_d -> False),
  all_open_payload st ==>
  all_open_payload (shvec_replace_ith sdenote_desc (projT2 d) st i v).
Proof.
  intros. now apply all_open_payload_replace'.
Qed.

Definition run_init_cmd :
  forall (prog_envd : vdesc) (s : init_state prog_envd)
         (c : cmd prog_envd (base_term prog_envd)),
  STsep (tr :~~ init_ktr prog_envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state prog_envd => tr :~~ init_ktr prog_envd s' in
          init_invariant s' * traced (expand_ktrace tr) *
          [exists input, s' = init_state_run_cmd prog_envd s c input]).
Proof.
  intros; destruct s as [cs tr e st fds]_eqn; refine (
    match c with

    | Send fe t me =>
      (* /!\ We lose track of the let-open equalities if existentials remain,
         make sure that Coq can infer _all_ the underscores. *)
      let f := eval_base_expr _ e fe in
      let m := eval_base_payload_expr _ e _ me in
      send_msg f (Build_msg t m) (tr ~~~ expand_ktrace tr)
      <@> open_payload_frame_base_expr e cs fds fe f;;

      let tr := tr ~~~ KSend f (Build_msg t m) :: tr in
      {{ Return {| init_comps := cs
                 ; init_ktr   := tr
                 ; init_env   := e
                 ; init_kst   := st
                 ; init_fds   := fds
                 |} }}

    | Spawn ct cfg i EQ =>
      let c_cmd := compd_cmd (COMPS ct) in
      let c_args := compd_args (COMPS ct) in
      c <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
      <@> init_invariant s;

      let tr := tr ~~~ KExec c_cmd c_args c :: tr in
      {{ Return {| init_comps := {| comp_type := ct; comp_fd := c; comp_conf := cfg |} :: cs
                 ; init_ktr   := tr
                 ; init_env   := shvec_replace_cast _ EQ e c
                 ; init_kst   := st
                 ; init_fds   := FdSet.add c fds
                 |} }}

    | StUpd i ve =>
      let v := eval_base_expr _ e ve in
      {{ Return {| init_comps := cs
                 ; init_ktr   := tr
                 ; init_env   := e
                 ; init_kst   := shvec_replace_ith _ _ st i v
                 ; init_fds   := fds
                 |} }}

    end
  ); sep''; try subst v; sep'; simpl in *.

  unfold f.
  refine (
  match fe as _fe in expr _ _d return
    let _f := eval_base_expr prog_envd e _fe in
    _d = fd_d ->
    all_open_set fds ==>
    open_if_fd _d _f
    * open_payload_frame_base_expr' fds _fe _f
  with
  | Term _ t => _
  | UnOp _ _ op e => _
  | BinOp _ _ _ op e1 e2 => _
  end (Logic.eq_refl fd_d)
  ); intros _f EQ; unfold _f; clear _f.
  destruct t0; try congruence.
  simpl in *.
  refine (
  match svec_ith (projT2 prog_envd) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    all_open_set fds ==>
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 prog_envd) e i)
  ); simpl in *.
  admit. (* easy *)
  destruct op; try congruence.
  destruct op; try congruence.

  isolate (
    traced (trace_send_msg f {| tag := t; pay := m |} ++ expand_ktrace x0)
    ==>
    traced (expand_ktrace x2)
  ).
  admit. (* TODO: figure out why sep'' does not solve this *)

  unfold f.
  refine (
  match fe as _fe in expr _ _d return
    let _f := eval_base_expr prog_envd e _fe in
    _d = fd_d ->
    open_if_fd _d _f
    * open_payload_frame_base_expr' fds _fe _f
    ==> all_open_set fds
  with
  | Term _ t => _
  | UnOp _ _ op e => _
  | BinOp _ _ _ op e1 e2 => _
  end (Logic.eq_refl fd_d)
  ); intros _f EQ; unfold _f; clear _f.
  destruct t0; try congruence.
  simpl in *.
  refine (
  match svec_ith (projT2 prog_envd) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
    ==> all_open_set fds
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 prog_envd) e i)
  ); simpl in *.
  admit. (* easy *)
  destruct op; try congruence.
  destruct op; try congruence.

  exists tt. unfold tr0. sep''.

  isolate (
    traced (Exec c_cmd c_args c0 :: expand_ktrace x0)
    ==> traced (expand_ktrace x2)
  ).
  admit. (* TODO: figure out why sep'' does not solve this *)

  admit. (* TODO easy *)

  exists c0. unfold tr0. sep''.

  admit. (* TODO medium *)

  constructor. simpl. apply FdSet.add_spec. now left.
  admit. (* TODO easy *)

  exists tt.  sep''.
Qed.

Definition run_init_prog :
  forall (envd : vdesc) (s : init_state envd) (p : init_prog envd),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr)
          * [exists input, s' = init_state_run_prog envd s p input]).
Proof.
  intros; refine (
    Fix2
      (fun p s => tr :~~ init_ktr envd s in
        init_invariant s * traced (expand_ktrace tr))
      (fun p s (s' : init_state envd) => tr :~~ init_ktr envd s' in
        init_invariant s' * traced (expand_ktrace tr)
        * [exists input, s' = init_state_run_prog envd s p input])
      (fun self p s =>
        match p with
        | nil => {{ Return s }}
        | c::cs =>
          s' <- run_init_cmd envd s (c s);
          s'' <- self cs s' <@> [exists input, s' = init_state_run_cmd envd s (c s) input];
          {{ Return s'' }}
        end
      )
    p s
  ); sep''.
  exists tt. reflexivity.
  destruct H3 as [i1 I1]. destruct H4 as [i2 I2]. subst s'.
  exists (existT
            (fun x : cmd_input envd (c s0) =>
               init_state_run_prog_return_type envd
                 (init_state_run_cmd envd s0 (c s0) x) cs)
            i2 i1). assumption.
Qed.

Theorem all_open_default_payload : forall henv,
  emp ==> all_open_payload (default_payload henv).
Proof.
  intros [n envd]. induction n.
  unfold all_open_payload, all_open_payload'. now simpl.
  destruct envd as [d envd']. unfold default_payload. simpl.
  destruct d.
  exact (IHn envd').
  exact (IHn envd').
  unfold all_open_payload, all_open_payload'. simpl.
  isolate (emp ==> open devnull). exact devnull_open.
  exact (IHn envd').
Qed.

Definition all_open_payload_to_all_open : forall v p,
  all_open_payload p ==> all_open (payload_fds v p).
Proof.
  admit.
Qed.

Theorem all_open_concat : forall a b,
  all_open a * all_open b ==> all_open (a ++ b).
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
Qed.

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    let s := initial_init_state in
    s' <- run_init_prog _ s IPROG;
    {{ Return {| kcs := init_comps _ s'
               ; ktr := init_ktr _ s'
               ; kst := init_kst _ s'
               ; kfd := FdSet.union
                          (payload_fds_set KSTD (init_kst IENVD s'))
                          (payload_fds_set IENVD (init_env IENVD s'))
               |}
     }}
  ); sep''.
  admit.
  admit.
  admit.
  admit.
  destruct H4 as [i4 I4].
  now apply Reach_init with (input := i4).
  admit.
  admit.
Qed.

Lemma env_fds_in_app_r : forall envd env a b,
  env_fds_in a envd env ->
  env_fds_in (b ++ a) envd env.
Proof.
  intros. induction b. now simpl. simpl. unfold env_fds_in in *.
  intros i. specialize (IHb i). clear H.
  generalize dependent (shvec_ith sdenote_desc (projT2 envd) env i).
  destruct (svec_ith (projT2 envd) i); try tauto.
  intros. now right.
Qed.

Definition run_hdlr_cmd :
  forall (cfd : fd) (cm : msg) (envd : vdesc) (s : hdlr_state envd)
         (c : cmd envd (hdlr_term cm envd)),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
          * [exists input, s' = hdlr_state_run_cmd cfd cm envd s c input]).
Proof.
  intros; destruct s as [ [ cs tr st fds ] env]_eqn; refine (
  match c with

  | Send fe t me =>
    let f := eval_hdlr_expr cfd cm envd env st fe in
    let m := eval_hdlr_payload_expr cfd cm envd st env _ me in
    send_msg f (Build_msg t m)
    (tr ~~~ expand_ktrace tr)
    <@> open_payload_frame_hdlr_expr env cs cm cfd fds fe f;;

    let tr := tr ~~~ KSend f (Build_msg t m) :: tr in
    {{Return {| hdlr_kst := {| kcs := cs ; ktr := tr ; kst := st ; kfd := fds |}
              ; hdlr_env := env
              |}
    }}

  | Spawn ct cfg i EQ =>
    let c_cmd := compd_cmd (COMPS ct) in
    let c_args := compd_args (COMPS ct) in
    c <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cfd cm s;

    let tr := tr ~~~ KExec c_cmd c_args c :: tr in
    {{ Return {| hdlr_kst := {| kcs := {| comp_type := ct; comp_fd := c; comp_conf := cfg |} :: cs
                              ; ktr := tr
                              ; kst := st
                              ; kfd := FdSet.add c fds |}
               ; hdlr_env := shvec_replace_cast _ EQ env c
               |}
    }}

  | StUpd i ve =>
    let v := eval_hdlr_expr cfd cm envd env st ve in
    {{ Return {| hdlr_kst := {| kcs := cs
                              ; ktr := tr
                              ; kst := shvec_replace_ith _ _ st i v
                              ; kfd := fds
                              |}
               ; hdlr_env := env
               |}
    }}

  end
  ); sep''; try subst v; sep'; simpl in *.

  unfold f.
  refine (
  match fe as _fe in expr _ _d return
    let _f := eval_hdlr_expr cfd cm envd env st _fe in
    _d = fd_d ->
    all_open_set fds ==>
    open_if_fd _d _f
    * open_payload_frame_hdlr_expr' cfd fds _fe _f
  with
  | Term _ t => _
  | UnOp _ _ op e => _
  | BinOp _ _ _ op e1 e2 => _
  end (Logic.eq_refl fd_d)
  ); intros _f EQ; unfold _f; clear _f.
  destruct t0; try congruence; simpl in *.
  destruct b; try congruence; simpl in *.
  refine (
  match svec_ith (projT2 envd) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    all_open_set fds ==>
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 envd) env i)
  ); simpl in *.
  admit. (* easy *)
  admit. (* easy *)
  refine (
  match svec_ith (projT2 (CPAY cm)) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    all_open_set fds ==>
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 (CPAY cm)) (pay cm) i)
  ); simpl in *.
  admit. (* easy *)
  refine (
  match svec_ith KSTD_DESC i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    all_open_set fds ==>
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc KSTD_DESC st i)
  ); simpl in *.
  admit. (* easy *)
  destruct op; try congruence.
  destruct op; try congruence.

  isolate (
    traced (trace_send_msg f {| tag := t; pay := m |} ++ expand_ktrace x0)
    ==>
    traced (expand_ktrace x2)
  ).
  admit. (* TODO: figure out why sep'' does not solve this *)

  unfold f.
  refine (
  match fe as _fe in expr _ _d return
    let _f := eval_hdlr_expr cfd cm envd env st _fe in
    _d = fd_d ->
    open_if_fd _d _f
    * open_payload_frame_hdlr_expr' cfd fds _fe _f
    ==> all_open_set fds
  with
  | Term _ t => _
  | UnOp _ _ op e => _
  | BinOp _ _ _ op e1 e2 => _
  end (Logic.eq_refl fd_d)
  ); intros _f EQ; unfold _f; clear _f.
  destruct t0; try congruence; simpl in *.
  destruct b; try congruence; simpl in *.
  refine (
  match svec_ith (projT2 envd) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
    ==> all_open_set fds
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 envd) env i)
  ); simpl in *.
  admit. (* easy *)
  admit. (* easy *)
  refine (
  match svec_ith (projT2 (CPAY cm)) i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
    ==> all_open_set fds
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc (projT2 (CPAY cm)) (pay cm) i)
  ); simpl in *.
  admit.
  refine (
  match svec_ith KSTD_DESC i as _s return
    _s = fd_d -> forall (v : s[[_s]]),
    open_if_fd _s v *
    match _s as __s return sdenote_desc __s -> hprop with
    | fd_d => fun f => all_open_set_drop f fds
    | _ => fun _ => emp
    end v
    ==> all_open_set fds
  with
  | fd_d => fun _ f'' => _
  | num_d => fun EQ _ _ => False_rec _ (numd_neq_fdd EQ)
  | str_d => fun EQ _ _ => False_rec _ (strd_neq_fdd EQ)
  end EQ (shvec_ith sdenote_desc KSTD_DESC st i)
  ); simpl in *.
  admit. (* easy *)
  destruct op; try congruence.
  destruct op; try congruence.

  exists tt. unfold tr0. sep''.

  rewrite Heqh. simpl. sep''.

  isolate (
    traced (Exec c_cmd c_args c0 :: expand_ktrace x0)
    ==> traced (expand_ktrace x2)
  ).
  admit. (* TODO: figure out why sep'' does not solve this *)
  admit. (* easy *)
  admit. (* easy *)
  admit. (* medium *)
  admit. (* easy *)
  admit. (* easy *)

  exists c0. unfold tr0. sep''.

  exists tt.  sep''.
Qed.

Definition run_hdlr_prog :
  forall (cfd : fd) (cm : msg) (envd : vdesc) (s : hdlr_state envd) (p : hdlr_prog cm envd),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
          * [exists input, s' =
               hdlr_state_run_prog cfd _ envd s (p (hdlr_kst _ s)) input]).
Proof.
  intros; refine (
    Fix2
      (fun p (s : hdlr_state envd) =>
        tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
      (fun p s (s' : hdlr_state envd) =>
        tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
                                            (* TODO: this works but seems wrong *)
          * [exists input, s' = hdlr_state_run_prog cfd _ envd s p input])
      (fun self p s =>
        match p with
        | nil =>
          {{ Return s }}
        | c::cs =>
          s' <- run_hdlr_cmd cfd cm envd s (c (hdlr_kst _ s));
          s'' <- self cs s'
          <@> [exists input, s' = hdlr_state_run_cmd cfd _ envd s (c (hdlr_kst _ s)) input];
          {{ Return s'' }}
        end)
    (p (hdlr_kst _ s)) s
  );
  sep''.
  now exists tt.
  destruct H1 as [i1 I1]. destruct H2 as [i2 I2]. subst s'.
  exists (existT
            (fun x : cmd_input envd (c (hdlr_kst envd s0)) =>
               hdlr_state_run_prog_return_type cfd _ envd
                 (hdlr_state_run_cmd cfd _ envd s0 (c (hdlr_kst envd s0)) x) cs)
            i2 i1). exact I1.
Qed.

Theorem all_open_unconcat : forall a b,
  all_open (a ++ b) ==> all_open a * all_open b.
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
Qed.

Axiom in_devnull_default_payload: forall henv l,
  env_fds_in (devnull :: l) henv (default_payload henv).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intro s; destruct s as [cs tr st fds]_eqn; refine (
    c <- select (proj_fds cs)
    (tr ~~~ expand_ktrace tr)
    <@> all_open_set fds * [Reach s] * [all_fds_in cs fds] * [pl_fds_subset st fds];

    let tr := tr ~~~ KSelect (proj_fds cs) c :: tr in
    mm <- recv_msg c
    (tr ~~~ expand_ktrace tr)
    <@> all_open_set_drop c fds * [FdSet.In c fds] * [Reach s] * [all_fds_in cs fds]
      * [pl_fds_subset st fds];

    match mm with
    | inl m =>
      let tr := tr ~~~ KRecv c m :: tr in
      let henv  := projT1 (HANDLERS m c) in
      let hprog := projT2 (HANDLERS m c) in
      let s' := {| hdlr_kst := {| kcs := cs
                                ; ktr := tr
                                ; kst := st
                                ; kfd := FdSet.union (payload_fds_set _ (pay m)) fds |}
                 ; hdlr_env := default_payload henv
                 |}
      in
      s'' <- run_hdlr_prog c m henv s' hprog
      <@> [Reach s];
      {{ Return (hdlr_kst _ s'') }}
    | inr m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{ Return {|kcs := cs; ktr := tr; kst := st; kfd := fds |} }}
    end

  ); sep''; try subst v; sep'; simpl in *.

  isolate (
    traced (Select (proj_fds cs) c :: expand_ktrace x0) ==>
    traced (expand_ktrace x)
  ).
  admit.
  admit. (* easy *)

  admit. (* combine 'In c (proj_fds cs)' and 'all_fds_in cs fds' *)

  (*unfold s'. simpl.*)
  isolate (
    traced (trace_recv_msg c m ++ expand_ktrace x0) ==>
    traced (expand_ktrace x3)
  ).
  admit.
  discharge_pure.
  admit. (* TODO *)
  admit.
  admit.
  admit.
  admit.

  destruct s'' as [kst'' env'']_eqn. simpl in *.
  discharge_pure.
  admit.

  admit.

  admit.

  destruct H4 as [i I]. rewrite I.
  eapply Reach_valid with (tr := x1) (input := i); eauto.
  rewrite Heqk. now simpl.
  rewrite Heqk. simpl. f_equal.
  admit.

  isolate (
    traced (trace_recv_bogus_msg c m ++ expand_ktrace x0) ==>
    traced (expand_ktrace x3)
  ).
  admit.
  admit.

  unfold tr1, tr0 in *.
  eapply Reach_bogus with (s := s); sep''.
Qed.

Definition kloop:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    Fix
      (fun s => kstate_inv s)
      (fun s s' => kstate_inv s')
      (fun self s =>
        s <- kbody s;
        s <- self s;
        {{ Return s }}
      )
    s
  );
  sep'.
Qed.

Definition main:
  forall (_ : unit),
  STsep (traced nil)
        (fun s' => kstate_inv s').
Proof.
  intros; refine (
    s0 <- kinit tt;
    sN <- kloop s0;
    {{ Return sN }}
  );
  sep'.
Qed.

End WITH_HANDLER.

End WITH_PAYLOAD_DESC_VEC.
