Require Import Ascii.
Require Import Eqdep_dec.
Require Import NPeano.
Require Import List.
Require Import String.
Require Import Ynot.

Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexVec.
Require Import ReflexHVec.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.
Open Scope list_scope.

Axiom TODO' : False. Definition TODO {A : Type} : A := match TODO' with end.

Ltac sep' := sep fail idtac.
Ltac inv H := inversion H; subst; clear H.

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
Context {VVD : vvdesc NB_MSG}.

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

Context {KST_DESC_SIZE : nat}.
Variable KST_DESC : vdesc' KST_DESC_SIZE.

Record kstate : Set := mkst
  { kcs : list fd
  ; ktr : [KTrace]
  ; kst : s[[ KST_DESC ]]
  ; kfd : list fd (* need to keep track of all the open fds... *)
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

(*
Notation unop d := (existT (fun n => vdesc' n) 1 (d, tt)).
Notation binop a b := (existT (fun n => vdesc' n) 2 (a, (b, tt))).

Inductive op : vdesc -> desc -> Set :=
(* unary *)
| Not : op (unop num_d) num_d
(* binary *)
| Eq :  forall (d : desc), op (binop d d) num_d
| Add : op (binop num_d num_d) num_d
| Sub : op (binop num_d num_d) num_d
| Mul : op (binop num_d num_d) num_d
| Cat : op (binop str_d str_d) str_d
.

Definition eval_op {args res} (o : op args res) : s[[ args ]] -> s[[ res ]] :=
  match o in op _args _res  return
    sdenote_vdesc _args -> s[[ _res ]]
  with
  | Not => fun args =>
    let (v, _) := args in
    if num_eq v FALSE then TRUE else FALSE
  | Eq d => fun args =>
    match args with (v1, (v2, _)) =>
      let teq : forall (x y : s[[ d ]]), {x = y} + {x <> y} :=
        match d with
        | num_d => num_eq
        | str_d => str_eq
        | fd_d  => fd_eq
        end
      in
      if teq v1 v2 then TRUE else FALSE
    end
  | Add => fun args =>
    match args with (v1, (v2, _)) =>
      num_of_nat (plus (nat_of_num v1) (nat_of_num v2))
    end
  | Sub => fun args =>
    match args with (v1, (v2, _)) =>
      num_of_nat (minus (nat_of_num v1) (nat_of_num v2))
    end
  | Mul => fun args =>
    match args with (v1, (v2, _)) =>
      num_of_nat (mult (nat_of_num v1) (nat_of_num v2))
    end
  | Cat => fun args =>
    match args with (v1, (v2, _)) =>
      v1 ++ v2
    end
  end.
*)

Section WITHIN_HANDLER.

Variable CST : kstate.
Variable CFD : fd.
Variable CMSG : msg.

Let CPAY : vdesc := lkup_tag (tag CMSG).

Definition payload_ith (vd : vdesc) :
  sdenote_vdesc vd -> forall (i : fin (projT1 vd)), s[[ svec_ith (projT2 vd) i ]] :=
  match vd as _vd with existT n pd => fun p i =>
    shvec_ith sdenote_desc pd p i
  end.

Definition msg_param_i (i : fin (projT1 CPAY)) : s[[ svec_ith (projT2 CPAY) i ]] :=
  payload_ith CPAY (pay CMSG) i.

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
  end (payload_ith envd env i).

Definition msg_fds_ok : Prop :=
  forall i,
  let d := svec_ith (projT2 CPAY) i in
  match d as _d return s[[ _d ]] -> Prop with
  | fd_d => fun (f : s[[ fd_d ]]) => In f (kcs CST)
  | _ => fun _ => True
  end (msg_param_i i).

Definition msg_fds_ck : decide msg_fds_ok.
Proof.
  apply forall_fin. intros i. generalize (msg_param_i i).
  destruct (svec_ith (projT2 CPAY) i).
  now left. now left.
  intros s. destruct CST as [comps ktr]. simpl in *. apply in_dec. exact fd_eq.
Qed.

(*
Definition msg_fds_ok : hprop := all_open_payload (pay CMSG).

Definition msg_fds_in : Prop := env_fds_in (components CST) CPAY (pay CMSG).

Definition decide_msg_fds_in : decide msg_fds_in.
Proof.
  apply forall_fin. intros i. generalize (payload_ith CPAY (pay CMSG) i).
  destruct (svec_ith (projT2 CPAY) i).
  now left. now left.
  intros s. destruct CST as [comps ktr]. simpl in *. apply in_dec. exact fd_eq.
Qed.
*)

Section WITH_ENVD.

Variable ENVD : vdesc.

Inductive base_expr : desc -> Set :=
| NLit : num -> base_expr num_d
| SLit : str -> base_expr str_d
| Var : forall (i : fin (projT1 ENVD)), base_expr (svec_ith (projT2 ENVD) i)
| UnOp : forall d1 d2, unop d1 d2 -> base_expr d1 -> base_expr d2
| BinOp : forall d1 d2 d3, binop d1 d2 d3 -> base_expr d1 -> base_expr d2 -> base_expr d3
.

Fixpoint payload_expr' (n : nat) (pd : vdesc' n) : Type :=
  match n as _n return vdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vdesc' (S n')) =>
    match pd with
    | (d, pd') => base_expr d * payload_expr' n' pd'
    end
  end%type pd.

Definition payload_expr pd := payload_expr' (projT1 pd) (projT2 pd).

Inductive expr_desc :=
| base_expr_d : desc -> expr_desc
| msg_expr_d : expr_desc
.

Definition sdenote_expr_desc t :=
  match t with
  | base_expr_d d => s[[ d ]]
  | msg_expr_d => msg
  end.

Instance SDenoted_expr_t : SDenoted expr_desc :=
{ sdenote := sdenote_expr_desc
}.

Inductive expr : expr_desc -> Type :=
(* an expression evaluating to one constant *)
| MEbase : forall d, base_expr d -> expr (base_expr_d d)
(* an expression evaluating to a vector of constants *)
| MEmsg : forall tag, payload_expr (lkup_tag tag) -> expr msg_expr_d
.

(* Within a handler, an expression may also refer to handler-specific things *)
Inductive hdlr_expr : expr_desc -> Type :=
| HEexpr : forall d, expr d -> hdlr_expr d
| HEchan : hdlr_expr (base_expr_d fd_d)
| HEparam : forall (i : fin (projT1 CPAY)),
  hdlr_expr (base_expr_d (svec_ith (projT2 CPAY) i))
(* Here should be HEkst or something to access a kstate variable *)
.

Section WITH_ENV.

Variable ENV : s[[ ENVD ]].

Fixpoint eval_base_expr (d : desc) (e : base_expr d) : s[[ d ]] :=
  match e in base_expr _d return sdenote_desc _d with
  | NLit n => n
  | SLit s => s
  | Var i => payload_ith ENVD ENV i
  | UnOp t1 t2 op e =>
    let v := eval_base_expr t1 e in
    eval_unop op v
  | BinOp t1 t2 t3 op e1 e2 =>
    let v1 := eval_base_expr t1 e1 in
    let v2 := eval_base_expr t2 e2 in
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
      (eval_base_expr d v, eval_payload_expr' n' pd' e')
  end.

Definition eval_payload_expr (pd : vdesc) (e : payload_expr pd) : s[[ pd ]] :=
  eval_payload_expr' (projT1 pd) (projT2 pd) e.

Definition eval_expr (d : expr_desc) (e : expr d) : s[[ d ]] :=
  match e with
  | MEbase d' e' => eval_base_expr d' e'
  | MEmsg t pl =>
    let p := eval_payload_expr (lkup_tag t) pl in
    {| tag := t; pay := p |}
  end.

Definition eval_hdlr_expr (d : expr_desc) (e : hdlr_expr d) : s[[ d ]] :=
  match e with
  | HEexpr d' e' => eval_expr d' e'
  | HEchan => CFD
  | HEparam i => msg_param_i i
  end.

Inductive cmd (e : expr_desc -> Type) : Type :=
| Send : e (base_expr_d fd_d) -> expr msg_expr_d -> cmd e
.

Definition init_cmd := cmd expr.

Definition init_prog := list init_cmd.

Definition hdlr_cmd := cmd hdlr_expr.

Definition hdlr_prog := list hdlr_cmd.

End WITH_ENV.

Record init_state :=
{ init_comps : list fd
; init_ktr   : [KTrace]%type
; init_env   : s[[ ENVD ]]
}.

Definition init_state_run_cmd (s : init_state) : init_cmd -> init_state :=
  let (cs, tr, e) := s in
  fun c =>
    match c with
    | Send fe me =>
      let f := eval_expr e _ fe in
      let m := eval_expr e _ me in
      {| init_comps := cs
       ; init_ktr   := tr ~~~ KSend f m :: tr
       ; init_env   := e
      |}
    end.

Fixpoint init_state_run_prog (s : init_state) (p : init_prog) : init_state :=
  match p with
  | c :: cs => init_state_run_prog (init_state_run_cmd s c) cs
  | nil => s
  end.

Record hdlr_state :=
{ hdlr_kst : kstate
; hdlr_env : s[[ ENVD ]]
}.

(* This should probably move out once the environment can change *)
Definition hdlr_state_run_cmd (s : hdlr_state) : hdlr_cmd -> hdlr_state :=
  let (s', env) := s in
  let (cs, tr, st, fd) := s' in
  fun c =>
    match c with
    | Send fe me =>
      let f := eval_hdlr_expr env _ fe in
      let m := eval_expr env _ me in
      {| hdlr_kst :=
           {| kcs := cs
            ; ktr := tr ~~~ KSend f m :: tr
            ; kst := st
            ; kfd := fd
            |}
       ; hdlr_env := env
      |}
    end.

Fixpoint hdlr_state_run_prog (s : hdlr_state) (p : hdlr_prog) : hdlr_state :=
  match p with
  | nil => s
  | c::cs => hdlr_state_run_prog (hdlr_state_run_cmd s c) cs
  end.

Axiom devnull : fd.

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

Fixpoint kstate_run_prog (s : kstate) (p : hdlr_prog) : kstate :=
  let hs :=
    {| hdlr_kst := s
     ; hdlr_env := default_payload ENVD
     |} in
  hdlr_kst (hdlr_state_run_prog hs p).

End WITH_ENVD.
End WITHIN_HANDLER.

Variable INIT_ENVD : vdesc.
Variable INIT_PROG : init_prog INIT_ENVD.
Variable MK_KSTATE : init_state INIT_ENVD -> kstate.

Definition initial_init_state :=
  {| init_comps := nil
   ; init_ktr   := [nil]%inhabited
   ; init_env   := default_payload INIT_ENVD
   |}.

Section WITH_HANDLER.

Variable HANDLER : forall (m : msg), sigT (fun (vd : vdesc) => hdlr_prog m vd).

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
  Reach (MK_KSTATE (init_state_run_prog INIT_ENVD initial_init_state INIT_PROG))
| Reach_valid :
  forall s f m tr s' s'' envdp,
  msg_fds_ok s m ->
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  s' = {| kcs := cs
        ; ktr := [KRecv f m :: KSelect cs f :: tr]
        ; kst := kst s
        ; kfd := kfd s
        |} ->
  s'' = kstate_run_prog f m (projT1 envdp) s' (projT2 envdp) ->
  Reach {| kcs := kcs s''
         ; ktr := ktr s''
         ; kst := kst s''
         ; kfd := kfd s'' ++ payload_fds _ (pay m)
         |}
| Reach_bad_fds :
  forall s f m tr,
  let cs := kcs s in
  ~ msg_fds_ok s m ->
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach {| kcs := cs
         ; ktr := [KRecv f m :: KSelect cs f :: tr]
         ; kst := kst s
         ; kfd := kfd s ++ payload_fds _ (pay m)
         |}
| Reach_bogus :
  forall s f bmsg tr,
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  Reach
    {| kcs := cs
     ; ktr := [KBogus f bmsg :: KSelect cs f :: tr]
     ; kst := kst s
     ; kfd := kfd s
     |}
.

Definition kstate_inv s : hprop :=
  tr :~~ ktr s in emp
  * traced (expand_ktrace tr) * [Reach s]
  * all_open (kcs s) * all_open (kfd s)
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
  | [ H : [_]%inhabited = [_]%inhabited |- _ ] =>
    apply pack_injective in H; subst
  end.

Ltac misc :=
  match goal with
  | [ |- Reach _ ] => econstructor; eauto
  end.

Ltac unfoldr :=
  unfold kstate_inv.

Ltac simplr :=
  sep';
  try uninhabit;
  try opens_packing;
  try misc.

Ltac sep'' :=
  sep unfoldr simplr.

Lemma eval_base_expr_fd :
  forall l d envd e v env,
  env_fds_in l envd env ->
  eval_base_expr envd env d e = v ->
  match d as _d return (s[[ _d ]] -> Prop) with
  | fd_d => fun f => In f l
  | _ => fun _ => True
  end v.
Proof.
  induction e; try tauto; intros vd env OK E; simpl in *.
  subst. exact (OK i).
  now destruct u.
  now destruct b.
Qed.

Lemma eval_expr_fd :
  forall l d envd e v env,
  env_fds_in l envd env ->
  eval_expr envd env d e = v ->
  match d as _d return (sdenote_expr_desc _d -> Prop) with
  | base_expr_d fd_d => fun f => In f l
  | _ => fun _ => True
  end v.
Proof.
  intros l d envd. induction e; intros vd env OK E; simpl in *.
  destruct b; try tauto; simpl in *.
  subst. exact (OK i).
  now destruct u.
  now destruct b1.
  exact I.
Qed.

Theorem eval_expr_fd_in_payload : forall envd d fe v s,
  eval_expr envd (init_env envd s) d fe = v ->
  match d as _d return sdenote_expr_desc _d -> Prop with
  | base_expr_d fd_d => fun f => fd_in_payload f envd (init_env envd s)
  | _ => fun _ => True
  end v.
Proof.
  intros envd d.
  destruct fe; intros v s E; intuition simpl in *.
  destruct b as []_eqn; intuition simpl in *. subst.
  pose proof (
    shvec_ith_in sdenote_desc desc_eqdec UIP_refl_desc (projT2 envd)
    (init_env envd s) i
  ).
  destruct envd as [n envd]. simpl in *.
  unfold payload_ith.
  generalize dependent (
    shvec_ith sdenote_desc envd
      (init_env (existT (fun n0 : nat => vdesc' n0) n envd) s) i
  ).
  intros.
  destruct (svec_ith envd i); tauto.
  now destruct u.
  now destruct b0.
Qed.

Definition init_invariant {envd} (s : init_state envd) :=
  all_open (init_comps _ s)
  * all_open_payload (init_env _ s).

Definition run_init_cmd :
  forall (envd : vdesc) (s : init_state envd) (c : init_cmd envd),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr) * [s' = init_state_run_cmd envd s c]).
Proof.
  intros; refine (
    let cs := init_comps _ s in
    let tr := init_ktr _ s in
    let e := init_env _ s in
    match c with
    | Send fe me =>
      (* /!\ We lose track of the let-open equalities if existentials remain,
         make sure that Coq can infer _all_ the underscores. *)
      let f := eval_expr _ e _ fe in
      let m := eval_expr _ e _ me in
      send_msg f m (tr ~~~ expand_ktrace tr)
      <@> all_open cs * all_open_payload_drop f e;;

      let tr := tr ~~~ KSend f m :: tr in
      {{ Return {| init_comps := cs; init_ktr := tr; init_env := e |} }}
    end
  ); unfold init_invariant, cs, e; sep''.
  pose proof eval_expr_fd_in_payload as E.
  specialize (E _ _ fe f s (Logic.eq_refl f)). now simpl in E.
  pose proof eval_expr_fd_in_payload as E.
  specialize (E _ _ fe f s (Logic.eq_refl f)). now simpl in E.
  apply himp_pure'.
  unfold init_state_run_cmd. destruct s. simpl.
  sep''. unfold f, m, e. simpl in *. sep''.
  (* dirty proof, could be made nicer... *)
Qed.

(* that seems wrong and unneeded
Fixpoint init_env_fds_ok' (n : nat) : forall (v : vdesc' n), sdenote_vdesc' n v -> hprop.
Proof.
  destruct n as [|n']. exact (fun _ _ => emp).
  intros v. destruct v as [d v']. destruct d.
  intros vv. destruct vv as (vd, vv'). exact (init_env_fds_ok' n' v' vv').
  intros vv. destruct vv as (vd, vv'). exact (init_env_fds_ok' n' v' vv').
  intros vv. destruct vv as (vd, vv'). exact (open vd * init_env_fds_ok' n' v' vv').
Qed.

(* is this needed? *)
Fixpoint init_env_fds_ok'' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> hprop :=
  match n with
  | 0 => fun _ _ => emp
  | S n0 =>
    fun v =>
    let (d, v') as p return (sdenote_vdesc' (S n0) p -> hprop) := v in
    fun vv =>
    let (vd, _) := vv in
    match d as d0 return (s[[d0]] -> hprop) with
    | fd_d => fun vd => open vd
    | _ => fun _ => emp
    end vd
  end
.
*)

Definition run_init_prog :
  forall (envd : vdesc) (s : init_state envd) (p : init_prog envd),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr) * [s' = init_state_run_prog envd s p]).
Proof.
  intros; refine (
    Fix2
      (fun p s => tr :~~ init_ktr envd s in
        init_invariant s * traced (expand_ktrace tr))
      (fun p s (s' : init_state envd) => tr :~~ init_ktr envd s' in
        init_invariant s' * traced (expand_ktrace tr) * [s' = init_state_run_prog envd s p])
      (fun self p s =>
        match p with
        | nil => {{ Return s }}
        | c::cs =>
          s' <- run_init_cmd envd s c;
          s'' <- self cs s' <@> [s' = init_state_run_cmd envd s c];
          {{ Return s'' }}
        end
      )
    p s
  ); sep''.
Qed.

(*
Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    let t3r := [nil]%inhabited in
    c <- exec init_str nil tr;
    let tr := tr ~~~ KExec init_str nil c :: nil in
    {{Return {|components := c :: nil; ktr := tr; kst := INIT_KST |}}}
  );
  sep''.
Qed.
*)

(*
Definition run_init_cmd :
  forall (envd : vdesc) (s : init_state envd) (c : init_cmd envd),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr) * [s' = init_state_run_cmd envd s c]).
*)

Definition env_fds_ok envd (hs : hdlr_state envd) :=
  env_fds_in (kfd (hdlr_kst envd hs)) envd (hdlr_env envd hs).

Theorem eval_hdlr_expr_fd_in : forall cfd cm envd d fe v (s : hdlr_state envd),
  let (kst, env) := s in
  env_fds_ok envd s ->
  msg_fds_ok kst cm ->
  In cfd (kcs kst) ->
  eval_hdlr_expr cfd cm envd env d fe = v ->
  match d as _d return sdenote_expr_desc _d -> Prop with
  | base_expr_d fd_d => fun f => In f (kcs kst) \/ In f (kfd kst)
  | _ => fun _ => True
  end v.
Proof.
  intros until s. destruct s as [kst env]. simpl. intros F M I E. subst.
  destruct fe; simpl in *; try tauto.
  destruct e; simpl in *; try tauto.
  destruct b; simpl in *; try tauto.
  specialize (F i). simpl in F.
  generalize dependent (payload_ith envd env i).
  destruct (svec_ith (projT2 envd) i); tauto.
  now destruct u.
  now destruct b1.
  specialize (M i). simpl in *.
  generalize dependent (msg_param_i cm i).
  destruct (svec_ith (projT2 (lkup_tag (tag cm))) i); tauto.
Qed.

Definition hdlr_invariant {envd} (cfd : fd) (cm : msg) (s : hdlr_state envd) :=
  let (kst, env) := s in
  all_open (kcs kst ++ kfd kst)
  * all_open_payload (pay cm) (* this might become problematic *)
  * [In cfd (kcs kst)] * [msg_fds_ok kst cm] * [env_fds_ok envd s]
.

Definition run_hdlr_cmd :
  forall (cfd : fd) (cm : msg) (envd : vdesc) (s : hdlr_state envd) (c : hdlr_cmd cm envd),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
          * [s' = hdlr_state_run_cmd cfd cm envd s c]).
Proof.
  intros; refine (
    (* you lose the equations if you try to let (st, env, fds) := s *)
    let st := hdlr_kst _ s in
    let env := hdlr_env _ s in
    let comps := kcs st in
    let tr := ktr st in
    let fds := kfd st in
    match c with
    | Send fe me =>
      let f := eval_hdlr_expr cfd cm _ env _ fe in
      let m := eval_expr envd env _ me in
      send_msg f m
      (tr ~~~ expand_ktrace tr)
      <@> all_open_drop (comps ++ fds) f * all_open_payload (pay cm)
      * [In cfd comps] * [msg_fds_ok st cm] * [env_fds_ok envd s];;

      let tr := tr ~~~ KSend f m :: tr in
      {{Return {| hdlr_kst := {| kcs := comps ; ktr := tr ; kst := kst st ; kfd := fds |}
                ; hdlr_env := env
                |}
      }}
    end
  ); unfold env, fds, hdlr_invariant in *; clear env fds; sep fail idtac;
  pose proof (eval_hdlr_expr_fd_in cfd cm _ _ fe f s) as E;
  destruct s as (kst, env).
  sep''.
  sep''.
  apply himp_pure'. destruct kst as (kcs, ktr, kst, kfd). simpl in *.
  unfold comps in *. clear comps. sep''.
  apply himp_pure'. destruct kst as (cs, ktr, kst, kfd). simpl in *.
  unfold comps in *. clear comps. sep''.
  (* so ugly... *)
Qed.

Definition run_hdlr_prog :
  forall (cfd : fd) (cm : msg) (envd : vdesc) (s : hdlr_state envd) (p : hdlr_prog cm envd),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
          * [s' = hdlr_state_run_prog cfd cm envd s p]).
Proof.
  intros; refine (
    Fix2
      (fun p (s : hdlr_state envd) =>
        tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cfd cm s * traced (expand_ktrace tr))
      (fun p s (s' : hdlr_state envd) =>
        tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cfd cm s' * traced (expand_ktrace tr)
          * [s' = hdlr_state_run_prog cfd cm envd s p])
      (fun self p s =>
        match p with
        | nil =>
          {{ Return s }}
        | c::cs =>
          s' <- run_hdlr_cmd cfd cm envd s c;
          s'' <- self cs s' <@> [hdlr_state_run_cmd cfd cm envd s c = s'];
          {{ Return s'' }}
        end)
    p s
  );
  sep''.
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

Theorem all_open_concat : forall a b,
  all_open a * all_open b ==> all_open (a ++ b).
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
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

Axiom all_open_payload_to_all_open : forall m,
  all_open_payload (pay m) ==> all_open (payload_fds _ (pay m)).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intro s.
  refine (
    let cs := kcs s in
    let tr := ktr s in
    let st := kst s in
    let fd := kfd s in
    c <- select cs
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [Reach s] * all_open cs * all_open fd);

    let tr := tr ~~~ KSelect cs c :: tr in
    mm <- recv_msg c
    (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ [In c cs] * [Reach s] * all_open_drop cs c * all_open fd);

    match mm with
    | inl m =>
      let tr := tr ~~~ KRecv c m :: tr in
      let ck := msg_fds_ck s m in
      match ck as ck' return ck = ck' -> _ with
      | left _ => fun _ =>
        match HANDLER m with existT henv hprog =>
        let s' := {| hdlr_kst := {| kcs := cs
                                  ; ktr := tr
                                  ; kst := st
                                  ; kfd := (*devnull ::*) fd |}
                   ; hdlr_env := default_payload henv
                   |}
        in
        s'' <- run_hdlr_prog c m henv s' hprog <@> [Reach s];
        (* we need to add the payload open fds to kfd so as not to keep track of any
           linear resource *)
        let s''' := {| hdlr_kst := {| kcs := kcs (hdlr_kst _ s'')
                                    ; ktr := ktr (hdlr_kst _ s'')
                                    ; kst := kst (hdlr_kst _ s'')
                                    ; kfd := kfd (hdlr_kst _ s'') ++ payload_fds _ (pay m) |}
                     ; hdlr_env := hdlr_env _ s''
                     |}
        in
        {{ Return (hdlr_kst _ s''') }}
        end
      | right _ => fun _ =>
        {{Return {|kcs := cs; ktr := tr; kfd := fd ++ payload_fds _ (pay m)|}}}
      end (refl_equal ck)
    | inr m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{Return {|kcs := cs; ktr := tr; kfd := fd|}}}
    end
  ); unfold hdlr_invariant in *; sep''.

  isolate (
    all_open_drop cs c * open c * all_open fd
    ==> all_open (cs ++ (*devnull ::*) fd)
  ).

  apply himp_trans with (Q := all_open cs * all_open fd); sep''.
  apply himp_trans with (Q := all_open cs * all_open ((*devnull ::*) fd)).
  sep''. (*apply devnull_open.*) apply all_open_concat.
  apply himp_pure'. unfold env_fds_ok. simpl. admit. (*apply in_devnull_default_payload.*)

  destruct (hdlr_state_run_prog c m henv s' hprog) as [kst'' env'']_eqn.
  simpl in *. sep''.
  isolate (
    all_open (kcs kst'' ++ kfd kst'') * all_open_payload (pay m)
    ==> all_open (kcs kst'') * all_open (kfd kst'' ++ payload_fds _ (pay m))
  ).
  apply himp_trans with
  (Q := all_open (kcs kst'') * all_open (kfd kst'') * all_open_payload (pay m)); sep''.
  apply all_open_unconcat.
  apply himp_trans with
  (Q := all_open (kfd kst'') * all_open (payload_fds _ (pay m))); sep''.
  apply all_open_payload_to_all_open.
  apply all_open_concat.

  sep''. constructor; auto.
  eapply Reach_valid with (s := s) (s' := (hdlr_kst _ s')) (envdp := existT _ henv hprog); eauto.
  unfold s'. simpl. unfold cs, st, fd. sep''.

  unfold kstate_run_prog. simpl.
  unfold s' in Heqh. rewrite Heqh. now simpl.

  isolate (
    all_open_payload (pay m) * all_open fd ==>
    all_open (fd ++ payload_fds (lkup_tag (tag m)) (pay m))
  ).
  eapply himp_trans; [ | apply all_open_concat ]. sep''.
  apply all_open_payload_to_all_open.

  sep''.
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

Record spec :=
{ NB_MSG   : nat
; PAY_DESC : payload_desc_vec NB_MSG
; HANDLERS : handler (PDV:=PAY_DESC)
}.

Definition mk_main (s : spec) := main (HANDLERS s).
