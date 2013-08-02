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

Definition comp_conf_desc compt := compd_conf (COMPS compt).

Record comp : Set :=
{ comp_type : COMPT
; comp_fd   : fd
; comp_conf : s[[ comp_conf_desc comp_type ]]
}.

Inductive cdesc :=
| Desc : desc -> cdesc
| Comp : COMPT -> cdesc
.

Definition sdenote_cdesc cd :=
  match cd with
  | Desc d => sdenote_desc d
  | Comp t => sigT (fun c : comp => comp_type c = t)
  end.

Instance SDenoted_cdesc : SDenoted cdesc :=
{ sdenote := sdenote_cdesc
}.

Definition vcdesc' : nat -> Set := svec cdesc.

Definition sdenote_vcdesc' n (pt : vcdesc' n) : Set :=
  shvec sdenote_cdesc pt.

Instance SDenoted_vcdesc' {n} : SDenoted (vcdesc' n) :=
{ sdenote := sdenote_vcdesc' n
}.

Definition vcdesc := (sigT vcdesc').
(*Definition vcdesc := (sigT (fun (n : nat) => vcdesc' n)).*)

Definition sdenote_vcdesc (v : vcdesc) : Set :=
  sdenote_vcdesc' (projT1 v) (projT2 v).

Instance SDenoted_vcdesc : SDenoted vcdesc :=
{ sdenote := sdenote_vcdesc
}.

Fixpoint vdesc_to_vcdesc' {n : nat} : vdesc' n -> vcdesc' n :=
  match n with
  | O => fun _ => tt
  | S n' => fun v =>
    match v with (d, v') => (Desc d, vdesc_to_vcdesc' v') end
  end.

Fixpoint vdesc_to_vcdesc (v : vdesc) : vcdesc :=
  match v with existT n v' => existT _ n (vdesc_to_vcdesc' v') end.

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

Variable trace_fun : fd -> forall (d : desc), s[[ Desc d ]] -> list Action.

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

Definition proj_fds : list comp -> list fd :=
  map (fun comp => comp_fd comp).

Fixpoint retrieve_comp_from_fd (cs : list comp) (f : fd) (p : in_fd f (proj_fds cs)) {struct cs}
  : (sigT (fun c : comp => comp_fd c = f /\ In c cs)).
Proof.
  induction cs.
  destruct p.
  simpl in p. destruct (fd_eq (comp_fd a) f).
  exists a. intuition.
  destruct (IHcs p) as [x I].
  exists x. intuition.
Defined.

Definition select_comp (cs : list comp) (tr : [Trace]) :
  STsep (tr ~~ traced tr)
        (fun c : comp => tr ~~ traced (Select (proj_fds cs) (comp_fd c) :: tr) * [In c cs]).
Proof.
  refine (
    s <- select (proj_fds cs) tr;
    let (c, I) := retrieve_comp_from_fd cs (projT1 s) (projT2 s) in
    {{ Return {| comp_type := comp_type c
               ; comp_fd   := projT1 s
               ; comp_conf := comp_conf c
               |}
     }}
  ); sep'.
  discharge_pure. destruct c. simpl in *. now rewrite H0 in H1.
Qed.

Inductive KAction : Set :=
| KExec   : str -> list str -> comp -> KAction
| KCall   : str -> list str -> fd -> KAction
| KSelect : list comp -> comp -> KAction
| KSend   : comp -> msg -> KAction
| KRecv   : comp -> msg -> KAction
| KBogus  : comp -> bogus_msg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args c => Exec cmd args (comp_fd c) :: nil
  | KCall cmd args pipe => Call cmd args pipe :: nil
  | KSelect cs c => Select (proj_fds cs) (comp_fd c) :: nil
  | KSend c m => trace_send_msg (comp_fd c) m
  | KRecv c m => trace_recv_msg (comp_fd c) m
  | KBogus c bm => trace_recv_bogus_msg (comp_fd c) bm
  end.

Fixpoint expand_ktrace (kt : KTrace) : Trace :=
  match kt with
  | nil => nil
  | ka :: kas => expand_kaction ka ++ expand_ktrace kas
  end.

Variable KSTD : vcdesc.
Notation KSTD_SIZE := (projT1 KSTD).
Notation KSTD_DESC := (projT2 KSTD).

Record kstate : Type := mkst
  { kcs : list comp
  ; ktr : [KTrace]
  ; kst : s[[ KSTD ]]
  ; kfd : FdSet.t (* need to keep track of all the open fds... *)
  }.

Inductive unop : cdesc -> cdesc -> Set :=
| Not : unop (Desc num_d) (Desc num_d)
| SplitFst : ascii -> unop (Desc str_d) (Desc str_d)
| SplitSnd : ascii -> unop (Desc str_d) (Desc str_d)
.

Definition splitAt c s :=
  let fix splitAt_aux c s r_res :=
    match s with
    | nil    => (List.rev r_res, nil)
    | h :: t =>
      if Ascii.ascii_dec h c then (List.rev r_res, t) else splitAt_aux c t (h :: r_res)
    end
  in splitAt_aux c s nil.

Definition eval_unop
  (d1 d2 : cdesc) (op : unop d1 d2) (v : s[[ d1 ]]) : s[[ d2 ]] :=
  match op in unop t1 t2 return s[[ t1 ]] -> s[[ t2 ]] with
  | Not => fun v => if num_eq v FALSE then TRUE else FALSE
  | SplitFst c => fun v : str =>
    fst (splitAt c v)
  | SplitSnd c => fun v : str =>
    snd (splitAt c v)
  end v.

Implicit Arguments eval_unop.

Inductive binop : cdesc -> cdesc -> cdesc -> Set :=
| Eq    : forall d, binop d d (Desc num_d)
| Add   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Sub   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Mul   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Cat   : binop (Desc str_d) (Desc str_d) (Desc str_d)
.

Definition eval_binop
  (d1 d2 d3: cdesc) (op : binop d1 d2 d3) (v1 : s[[ d1 ]]) (v2 : s[[ d2 ]]) : s[[ d3 ]] :=
  match op in binop _d1 _d2 _d3 return s[[ _d1 ]] -> s[[ _d2 ]] -> s[[ _d3 ]] with
  | Eq d =>
    match d as _d return s[[ _d ]] -> s[[ _d ]] -> _ with
    | Desc d => fun v1 v2 : s[[ Desc d ]] =>
      let teq : forall (x y : s[[ d ]]), {x = y} + {x <> y} :=
        match d with
        | num_d => num_eq
        | str_d => str_eq
        | fd_d  => fd_eq
        end
      in
      if teq v1 v2 then TRUE else FALSE
    | Comp ct => fun c1 c2 =>
      (* Assumption: comparing the file descriptors is enough *)
      if fd_eq (comp_fd (projT1 c1)) (comp_fd (projT1 c2)) then TRUE else FALSE
    end
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
Variable CC : comp.
Variable CMSG : msg.

Definition CTAG := tag CMSG.
Definition CT := comp_type CC.
Definition CPAY : vdesc := lkup_tag CTAG.
Definition CCONFD := comp_conf_desc CT.

(*This is never used.*)
(*Definition msg_param_i (i : fin (projT1 CPAY)) : s[[ svec_ith (projT2 CPAY) i ]] :=
  shvec_ith _ (projT2 CPAY) (pay CMSG) i.*)

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

Definition vdesc_fds_in l (envd : vdesc) (env : s[[ envd ]]) : Prop :=
  forall i,
  match svec_ith (projT2 envd) i as _d return s[[ _d ]] -> Prop with
  | fd_d => fun (f : s[[ fd_d ]]) => In f l
  | _ => fun _ => True
  end (shvec_ith _ (projT2 envd) env i).

Definition vcdesc_fds_in l (envd : vcdesc) (env : s[[ envd ]]) : Prop :=
  forall i,
  match svec_ith (projT2 envd) i as _d return s[[ _d ]] -> Prop with
  | Desc fd_d => fun (f : s[[ Desc fd_d ]]) => In f l
  | _ => fun _ => True
  end (shvec_ith _ (projT2 envd) env i).

Inductive base_term envd : cdesc -> Set :=
| SLit   : str -> base_term envd (Desc str_d)
| NLit   : num -> base_term envd (Desc num_d)
| Var    : forall (i : fin (projT1 envd)), base_term envd (svec_ith (projT2 envd) i)
| CompFd : forall ct, base_term envd (Comp ct) -> base_term envd (Desc fd_d)
.

(*I only want handler and all things it depends on to
 require a component type and message type. I don't want them
 to require a full message and component. This hopefully will
 eliminate the need to do some casts.*)
Inductive hdlr_term (ct : COMPT) (tag : fin NB_MSG) envd : cdesc -> Set :=
| Base  : forall {d}, base_term envd d -> hdlr_term ct tag envd d
| CComp   : hdlr_term ct tag envd (Comp ct)
| CConf : forall (i : fin (projT1 (comp_conf_desc ct))),
            hdlr_term ct tag envd (Desc (svec_ith (projT2 (comp_conf_desc ct)) i))
| MVar  : forall (i : fin (projT1 (lkup_tag tag))),
            hdlr_term ct tag envd (Desc (svec_ith (projT2 (lkup_tag tag)) i))
| StVar : forall (i : fin KSTD_SIZE), hdlr_term ct tag envd (svec_ith KSTD_DESC i)
.

Section WITH_TERM.

Variable TERM : vcdesc -> cdesc -> Set.

Inductive expr envd : cdesc -> Set :=
| Term  : forall {d}, TERM envd d -> expr envd d
| UnOp  : forall {d1 d2}, unop d1 d2 -> expr envd d1 -> expr envd d2
| BinOp : forall {d1 d2 d3}, binop d1 d2 d3 -> expr envd d1 -> expr envd d2 -> expr envd d3
.

Fixpoint payload_cexpr' envd (n : nat) (pd : vcdesc' n) : Type :=
  match n as _n return vcdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vcdesc' (S n')) =>
    match pd with
    | (d, pd') => expr envd d * payload_cexpr' envd n' pd'
    end
  end%type pd.

Definition payload_cexpr envd pd := payload_cexpr' envd (projT1 pd) (projT2 pd).

Fixpoint payload_expr' envd (n : nat) (pd : vdesc' n) : Type :=
  match n as _n return vdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vdesc' (S n')) =>
    match pd with
    | (d, pd') => expr envd (Desc d) * payload_expr' envd n' pd'
    end
  end%type pd.

Definition payload_expr envd pd := payload_expr' envd (projT1 pd) (projT2 pd).

Section WITH_PROG_KST.

Variable KST : s[[ KSTD ]].

Fixpoint eval_base_term {d} {envd : vcdesc} (env : s[[envd]]) (t : base_term envd d) : s[[ d ]] :=
  match t in base_term _ _d return
    s[[_d]]
  with
  | SLit s       => s
  | NLit n       => n
  | Var i        => shvec_ith _ (projT2 envd) env i
  | CompFd ct t' => comp_fd (projT1 (eval_base_term env t'))
  end.

Definition eval_hdlr_term {d envd} (t : hdlr_term CT CTAG envd d) env
  : s[[ d ]] :=
  match t with
  | Base _ bt => eval_base_term env bt
  | CComp       => existT _ CC (Logic.eq_refl CT)
  | CConf i   => shvec_ith _ (projT2 CCONFD) (comp_conf CC) i
  | MVar i    => shvec_ith _ (projT2 CPAY) (pay CMSG) i
  | StVar i   => shvec_ith _ (projT2 KSTD) KST i
  end.

Variable EVAL_TERM : forall (d : cdesc) envd, s[[envd]] -> TERM envd d -> s[[ d ]].

Fixpoint eval_expr {d envd} env (e : expr envd d) : s[[ d ]] :=
  match e with
  | Term _ t => EVAL_TERM _ _ env t
  | UnOp _ _ op e =>
    let v := eval_expr env e in
    eval_unop op v
  | BinOp _ _ _ op e1 e2 =>
    let v1 := eval_expr env e1 in
    let v2 := eval_expr env e2 in
    eval_binop op v1 v2
  end.

Fixpoint eval_payload_cexpr' envd env (n : nat) :
  forall (pd : vcdesc' n), payload_cexpr' envd n pd -> s[[ pd ]] :=
  let res n pd := payload_cexpr' envd n pd -> s[[ pd ]] in
  match n as _n return
    forall (pd : vcdesc' _n), res _n pd
  with
  | O => fun _ _ => tt
  | S n' => fun pd =>
    let (d, pd') as _pd return res (S n') _pd := pd in
    fun e =>
      let (v, e') := e in
      (eval_expr env v, eval_payload_cexpr' envd env n' pd' e')
  end.

Fixpoint eval_payload_expr' envd env (n : nat) :
  forall (pd : vdesc' n), payload_expr' envd n pd -> s[[ pd ]] :=
  let res n pd := payload_expr' envd n pd -> s[[ pd ]] in
  match n as _n return
    forall (pd : vdesc' _n), res _n pd
  with
  | O => fun _ _ => tt
  | S n' => fun pd =>
    let (d, pd') as _pd return res (S n') _pd := pd in
    fun e =>
      let (v, e') := e in
      (eval_expr env v, eval_payload_expr' envd env n' pd' e')
  end.

Definition eval_payload_cexpr envd env (pd : vcdesc) (e : payload_cexpr envd pd) : s[[ pd ]] :=
  eval_payload_cexpr' envd env (projT1 pd) (projT2 pd) e.

Definition eval_payload_expr envd env (pd : vdesc) (e : payload_expr envd pd) : s[[ pd ]] :=
  eval_payload_expr' envd env (projT1 pd) (projT2 pd) e.

Definition sdenote_desc_cfg_pat envd (d : desc) : Set := option (expr envd (Desc d)).

Record comp_pat envd : Set :=
{ comp_pat_type : COMPT
; comp_pat_conf : shvec (sdenote_desc_cfg_pat envd) (projT2 (comp_conf_desc comp_pat_type))
}.

Definition sdenote_desc_conc_pat (d : desc) : Set := option (s[[ d ]]).

Record conc_pat : Set :=
{ conc_pat_type : COMPT
; conc_pat_conf : shvec sdenote_desc_conc_pat (projT2 (comp_conf_desc conc_pat_type))
}.

Definition elt_match envd env (d : desc) (elt : s[[d]]) (elt' : sdenote_desc_cfg_pat envd d) : bool :=
  match elt' with
  | None   => true
  | Some x =>
    match d as _d return s[[_d]] -> s[[_d]] -> bool with
    | num_d => fun elt x => if num_eq x elt then true else false
    | str_d => fun elt x => if str_eq x elt then true else false
    | fd_d  => fun elt x => if fd_eq x elt then true else false
    end elt (eval_expr env x)
  end.

Definition match_comp_pf envd env (cp : comp_pat envd) (c : comp)
  : option (comp_type c = comp_pat_type _ cp) :=
  match COMPTDEC (comp_type c) (comp_pat_type _ cp) with
  | left EQ =>
    match EQ in _ = _t return
      shvec (sdenote_desc_cfg_pat envd) (projT2 (comp_conf_desc _t)) -> _
    with
    | Logic.eq_refl => fun cfgp =>
      if shvec_match (projT2 (comp_conf_desc (comp_type c)))
                     sdenote_desc (sdenote_desc_cfg_pat envd)
                     (elt_match envd env) (comp_conf c) cfgp
      then Some EQ
      else None
    end (comp_pat_conf _ cp)
  | right _ => None
  end.

Definition match_comp envd env (cp : comp_pat envd) (c : comp) : bool :=
  if match_comp_pf envd env cp c
  then true
  else false.

Fixpoint find_comp envd env (cp : comp_pat envd ) (comps : list comp)
  : option (sigT (fun c : comp => comp_type c = comp_pat_type _ cp)) :=
  match comps with
  | nil => None
  | c::comps' => match match_comp_pf envd env cp c with
                 | Some EQ => Some (existT _ c EQ)
                 | None    => find_comp envd env cp comps'
                 end
  end.

Definition filter_comps envd env (cp : comp_pat envd) (comps : list comp) :=
  filter (match_comp envd env cp) comps.

Definition exists_comp envd env (cp : comp_pat envd) (comps : list comp) :=
  match find_comp envd env cp comps with
  | None   => false
  | Some _ => true
  end.

Inductive cmd : vcdesc -> Type :=
| Nop : forall envd, cmd envd
| Seq : forall envd, cmd envd -> cmd envd -> cmd envd
| Ite : forall envd, expr envd (Desc num_d) -> cmd envd -> cmd envd -> cmd envd
| Send : forall envd ct, expr envd (Comp ct) -> forall (t : fin NB_MSG), payload_expr envd (lkup_tag t) -> cmd envd
(*| SendAll : forall envd, comp_pat envd -> forall (t : fin NB_MSG), payload_expr envd (lkup_tag t) -> cmd envd*)
| Spawn :
    forall (envd : vcdesc) (t : COMPT), s[[ comp_conf_desc t ]] ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Comp t -> cmd envd
| Call : forall (envd : vcdesc), expr envd (Desc str_d) -> list (expr envd (Desc str_d)) ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Desc fd_d -> cmd envd
| StUpd : forall envd i, expr envd (svec_ith (projT2 KSTD) i) -> cmd envd
| CompLkup : forall (envd : vcdesc) cp,
  cmd (existT _ (S (projT1 envd)) (svec_shift (Comp (comp_pat_type envd cp)) (projT2 envd))) ->
  cmd envd -> cmd envd
.

Record init_state (envd : vcdesc) :=
{ init_comps : list comp
; init_ktr   : [KTrace]%type
; init_env   : s[[ envd ]]
; init_kst   : s[[ KSTD ]]
; init_fds   : FdSet.t
}.

End WITH_PROG_KST.

End WITH_TERM.

Definition init_prog := cmd base_term.

Definition hdlr_prog (ct : COMPT) (tag : fin NB_MSG) := cmd (hdlr_term ct tag).

Inductive bintree T :=
| Leaf    : T -> bintree T
| NodeAnd : bintree T -> bintree T -> bintree T
.
Implicit Arguments Leaf [T].
Implicit Arguments NodeAnd [T].

Section WITH_EVAL_TERM.

Variable TERM : cdesc -> Set.
Variable EVAL_TERM : forall d, TERM d -> s[[d]].

Definition sdenote_option {T : Type} (sdenote_content : T -> Set) (o : option T) : Set :=
  match o with
  | Some x => sdenote_content x
  | None => unit
  end.

Fixpoint sdenote_bintree {T : Type} (sdenote_content : T -> Set) (t : bintree T) : Set :=
  match t with
  | Leaf l => sdenote_content l
  | NodeAnd l r =>
    (sdenote_bintree sdenote_content l * sdenote_bintree sdenote_content r)%type
  end.

Definition sdenote_input := sdenote_bintree (sdenote_option sdenote_cdesc).

End WITH_EVAL_TERM.

Definition shvec_replace_cast {d envd} {i : fin (projT1 envd)} (EQ : svec_ith (projT2 envd) i = d) e v
  :=
  shvec_replace_ith sdenote_cdesc _ e i
    (match EQ in _ = _d return s[[ _d ]] -> _ with Logic.eq_refl => fun x => x end v).

Definition eval_base_expr {d} {envd : vcdesc} : s[[envd]] -> expr base_term envd d -> s[[ d ]] :=
  eval_expr base_term (fun d envd e => @eval_base_term d envd e).

Definition eval_base_payload_cexpr :=
  eval_payload_cexpr base_term (fun d envd e => @eval_base_term d envd e).

Definition eval_base_payload_expr :=
  eval_payload_expr base_term (fun d envd e => @eval_base_term d envd e).

Definition eval_hdlr_expr {d} {envd : vcdesc} (s : s[[KSTD]])
  : s[[envd]] -> expr (hdlr_term CT CTAG) envd d -> s[[ d ]] :=
  eval_expr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).

Definition eval_hdlr_payload_cexpr s :=
  eval_payload_cexpr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).

Definition eval_hdlr_payload_expr s :=
  eval_payload_expr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).

Definition ktrace_send_msgs (cps : list comp) (m : msg) : KTrace :=
  (map (fun c => KSend c m) cps).

Inductive InputTreeType :=
| FD : InputTreeType
| Unit : InputTreeType
| Comb : InputTreeType -> InputTreeType -> InputTreeType.

Fixpoint run_cmd_it {envd : vcdesc} {term} (cmd : cmd term envd) : InputTreeType :=
  match cmd with
  | Spawn _ _ _ _ _ => FD
  | Call _ _ _ _ _ => FD
  | Seq _ c1 c2 => Comb (run_cmd_it c1)
                           (run_cmd_it c2)
  | Ite _ _ c1 c2 => Comb (run_cmd_it c1)
                             (run_cmd_it c2)
  | CompLkup _ _ c1 c2 => Comb (run_cmd_it c1)
                               (run_cmd_it c2)
  | _ => Unit
  end.

Fixpoint sdenote_itt (itt : InputTreeType) :=
  match itt with
  | FD => fd
  | Unit => unit
  | Comb l r => ((sdenote_itt l) * (sdenote_itt r))%type
  end.

Instance SDenoted_run_cmd_it : SDenoted InputTreeType :=
{
sdenote := sdenote_itt
}.

Fixpoint init_state_run_cmd (envd : vcdesc) (s : init_state envd) (cmd : cmd base_term envd)
  (input : s[[run_cmd_it cmd]]) : init_state envd :=
  match cmd as _cmd in cmd _ _envd return
    init_state _envd -> s[[run_cmd_it _cmd]] -> init_state _envd
  with
  | Nop _ => fun s _ => s

  | Seq envd c1 c2 => fun s i =>
    let s1 := init_state_run_cmd envd s c1 (fst i) in
    let s2 := init_state_run_cmd envd s1 c2 (snd i) in
    s2

  | Ite envd cond c1 c2 => fun s i =>
    if num_eq (@eval_base_expr (Desc num_d) _ (init_env _ s) cond) FALSE
    then init_state_run_cmd envd s c2 (snd i)
    else init_state_run_cmd envd s c1 (fst i)

  | Send _ ct ce t me => fun s _ =>
    let c := eval_base_expr (init_env _ s) ce in
    let m := eval_base_payload_expr _ (init_env _ s) _ me in
    let msg := (Build_msg t m) in
    let tr := init_ktr _ s in
    {| init_comps := init_comps _ s
     ; init_ktr   := tr ~~~ KSend (projT1 c) msg :: tr
     ; init_env   := init_env _ s
     ; init_kst   := init_kst _ s
     ; init_fds   := init_fds _ s
     |}

(*  | SendAll _ cp t me => fun s _ =>
    let m := eval_base_payload_expr _ (init_env _ s) _ me in
    let msg := (Build_msg t m) in
    let tr := init_ktr _ s in
    let cs := init_comps _ s in
    let comps := filter_comps base_term (fun d envd e => @eval_base_term _ _ e) _ (init_env _ s) cp cs in
    {| init_comps := cs
     ; init_ktr   := tr ~~~ ktrace_send_msgs comps msg ++ tr
     ; init_env   := init_env _ s
     ; init_kst   := init_kst _ s
     ; init_fds   := init_fds _ s
     |}*)

  | Spawn _ ct cfg i EQ => fun s i =>
    let tr := init_ktr _ s in
    let c_fd := i in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| init_comps := c :: (init_comps _ s)
     ; init_ktr   := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
     ; init_env   := shvec_replace_cast EQ (init_env _ s) (existT _ c (Logic.eq_refl _))
     ; init_kst   := init_kst _ s
     ; init_fds   := FdSet.add (comp_fd c) (init_fds _ s)
     |}

  | Call _ ce argse i EQ => fun s i =>
    let tr := init_ktr _ s in
    let f := i in
    let c := eval_base_expr (init_env _ s) ce in
    let args := map (eval_base_expr (init_env _ s)) argse in
    {| init_comps := init_comps _ s
     ; init_ktr   := tr ~~~ KCall c args f :: tr
     ; init_env   := shvec_replace_cast EQ (init_env _ s) f
     ; init_kst   := init_kst _ s
     ; init_fds   := FdSet.add f (init_fds _ s)
     |}

  | StUpd _ i ve => fun s _ =>
    let v := eval_base_expr (init_env _ s) ve in
    {| init_comps := init_comps _ s
     ; init_ktr   := init_ktr _ s
     ; init_env   := init_env _ s
     ; init_kst   := shvec_replace_ith _ _ (init_kst _ s) i v
     ; init_fds   := init_fds _ s
     |}

  | CompLkup envd cp c1 c2 => fun s i =>
    let ocdp := find_comp base_term (fun d envd e => @eval_base_term _ _ e) _ (init_env _ s)
      cp (init_comps _ s) in
    match ocdp with
    | Some cdp =>
      let c := projT1 cdp in
      let d := Comp (comp_pat_type _ _ cp) in
      let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
      let s' := Build_init_state new_envd (init_comps _ s) (init_ktr _ s)
                                 (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                                              (existT _ c (projT2 cdp)) (projT2 envd) (init_env _ s))
                                 (init_kst _ s) (init_fds _ s) in
      let s'' := init_state_run_cmd new_envd s' c1 (fst i) in
      {| init_comps := init_comps _ s''
       ; init_ktr   := init_ktr _ s''
       ; init_env   := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (init_env _ s'')
       ; init_kst   := init_kst _ s''
       ; init_fds   := init_fds _ s''
       |}
    | None   =>  init_state_run_cmd envd s c2 (snd i)
    end

  end s input.

Record hdlr_state (envd : vcdesc) :=
{ hdlr_kst : kstate
; hdlr_env : s[[ envd ]]
}.

(* This should probably move out once the environment can change *)
Fixpoint hdlr_state_run_cmd (envd : vcdesc) (s : hdlr_state envd) (cmd : cmd (hdlr_term CT CTAG) envd)
  (input : s[[run_cmd_it cmd]]) : hdlr_state envd :=
  match cmd as _cmd in cmd _ _envd return
    hdlr_state _envd -> s[[run_cmd_it _cmd]] -> hdlr_state _envd
  with
  | Nop _ => fun s _ => s

  | Seq envd c1 c2 => fun s i =>
    let s1 := hdlr_state_run_cmd envd s c1 (fst i) in
    let s2 := hdlr_state_run_cmd envd s1 c2 (snd i) in
    s2

  | Ite envd cond c1 c2 => fun s i =>
    if num_eq (@eval_hdlr_expr _ _ (kst (hdlr_kst _ s)) (hdlr_env _ s) cond) FALSE
    then hdlr_state_run_cmd envd s c2 (snd i)
    else hdlr_state_run_cmd envd s c1 (fst i)

  | Send _ ct ce t me => fun s _ =>
    let (s', env) := s in
    let c := eval_hdlr_expr (kst s') env ce in
    let m := eval_hdlr_payload_expr (kst s') _ env _ me in
    let msg := (Build_msg t m) in
    let tr := ktr s' in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := tr ~~~ KSend (projT1 c) msg :: tr
          ; kst := kst s'
          ; kfd := kfd s'
          |}
     ; hdlr_env := env
    |}

(*  | SendAll _ cp t me => fun s _ =>
    let (s', env) := s in
    let m := eval_hdlr_payload_expr (kst s') _ env _ me in
    let msg := (Build_msg t m) in
    let comps := filter_comps (hdlr_term CT CTAG)
      (fun d envd e t => @eval_hdlr_term (kst s') d envd t e) _ env cp (kcs s') in
    let tr := ktr s' in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := tr ~~~ ktrace_send_msgs comps msg ++ tr
          ; kst := kst s'
          ; kfd := kfd s'
          |}
     ; hdlr_env := env
    |}*)

  | Spawn _ ct cfg i EQ => fun s i =>
    let (s', env) := s in
    let tr := ktr s' in
    let c_fd := i in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| hdlr_kst :=
         {| kcs := c :: kcs s'
          ; ktr := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
          ; kst := kst s'
          ; kfd := FdSet.add (comp_fd c) (kfd s')
          |}
     ; hdlr_env := shvec_replace_cast EQ env (existT _ c (Logic.eq_refl _))
     |}

  | Call _ ce argse i EQ => fun s i =>
    let (s', env) := s in
    let tr := ktr s' in
    let f := i in
    let c := eval_hdlr_expr (kst s') env ce in
    let args := map (eval_hdlr_expr (kst s') env) argse in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := tr ~~~ KCall c args f :: tr
          ; kst := kst s'
          ; kfd := FdSet.add f (kfd s')
          |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}

  | StUpd _ i ve => fun s _ =>
    let (s', env) := s in
    let v := eval_hdlr_expr (kst s') env ve in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := ktr s'
          ; kst := shvec_replace_ith _ _ (kst s') i v
          ; kfd := kfd s'
          |}
     ; hdlr_env := env
     |}

  | CompLkup envd cp c1 c2 => fun s i =>
    let (s', env) := s in
    let ocdp := find_comp (hdlr_term CT CTAG)
      (fun d envd e t => @eval_hdlr_term (kst s') d envd t e) _ env cp (kcs s') in
    match ocdp with
    | Some cdp =>
      let c := projT1 cdp in
      let d := Comp (comp_pat_type _ _ cp) in
      let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
      let s' := Build_hdlr_state new_envd {| kcs := kcs s'
                                           ; ktr := ktr s'
                                           ; kst := kst s'
                                           ; kfd := kfd s'
                                           |}
                                (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                                              (existT _ c (projT2 cdp)) (projT2 envd) env) in
      let (ks'', new_env) := hdlr_state_run_cmd new_envd s' c1 (fst i) in
      {| hdlr_kst :=
           {| kcs := kcs ks''
            ; ktr := ktr ks''
            ; kst := kst ks''
            ; kfd := kfd ks''
            |}
       ; hdlr_env := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) new_env
       |}
    | None   =>  hdlr_state_run_cmd envd s c2 (snd i)
    end
  end s input.

Definition devnull := Num "000" "000".

Axiom devnull_open : emp ==> open devnull.

Fixpoint default_input {envd term} (c : cmd term envd) : s[[run_cmd_it c]] :=
  match c with
  | Spawn _ _ _ _ _ => devnull
  | Call _ _ _ _ _ => devnull
  | Seq _ c1 c2 => (default_input c1, default_input c2)
  | Ite _ _ c1 c2 => (default_input c1, default_input c2)
  | CompLkup _ _ c1 c2 => (default_input c1, default_input c2)
  | _ => tt
  end.

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

Definition axiomcomp (t : COMPT) : sigT (fun c : comp => comp_type c = t) :=
  let c := (Build_comp t devnull (default_payload _)) in
  existT _ c (Logic.eq_refl (comp_type c)).

Fixpoint default_cpayload' (n : nat) :
  forall (v : vcdesc' n), sdenote_vcdesc' n v :=
  match n with
  | O    => fun _ => tt
  | S n' => fun v =>
    match v with
    | (d, v') =>
      ( match d as _d return sdenote_cdesc _d with
        | Desc num_d => FALSE
        | Desc str_d => nil
        | Desc fd_f  => devnull
        | Comp ct    => axiomcomp ct
        end
      , default_cpayload' n' v')
    end
  end.

Definition default_cpayload (v : vcdesc) : s[[ v ]] :=
  default_cpayload' (projT1 v) (projT2 v).

Definition default_hdlr_state s envd :=
  {| hdlr_kst := s; hdlr_env := default_cpayload envd |}.

Definition kstate_run_prog envd (s : kstate) (p : hdlr_prog CT CTAG envd)
  (input : s[[run_cmd_it p]]) : kstate :=
  hdlr_kst envd (hdlr_state_run_cmd envd (default_hdlr_state s envd) p input).

End WITHIN_HANDLER.

Variable IENVD : vcdesc.

Variable IPROG : init_prog IENVD.

Definition initial_init_state :=
  {| init_comps := nil
   ; init_ktr   := [nil]%inhabited
   ; init_env   := default_cpayload IENVD
   ; init_kst   := default_cpayload KSTD
   ; init_fds   := FdSet.singleton devnull
   |}.

Section WITH_HANDLER.

Definition handlers := forall (tag : fin NB_MSG) (ct : COMPT),
  sigT (fun prog_envd => hdlr_prog ct tag prog_envd).

Variable HANDLERS : handlers.

Fixpoint vdesc_fds_set' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> FdSet.t :=
  match n with
  | 0 => fun _ _ => FdSet.empty
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> FdSet.t) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      FdSet.add vd (vdesc_fds_set' n' v' vv')
    | _ => fun vv =>
      let (_, vv') := vv in
      vdesc_fds_set' n' v' vv'
    end
  end.

Definition vdesc_fds_set (v : vdesc) : s[[ v ]] -> FdSet.t :=
  vdesc_fds_set' (projT1 v) (projT2 v).

Fixpoint vcdesc_fds_set' (n : nat) :
  forall (v : vcdesc' n), sdenote_vcdesc' n v -> FdSet.t :=
  match n as n return forall (v : vcdesc' n), sdenote_vcdesc' n v -> FdSet.t with
  | 0 => fun _ _ => FdSet.empty
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vcdesc' (S n') _v -> FdSet.t) := v in
    match d with
    | Desc fd_d => fun vv =>
      let (vd, vv') := vv in
      FdSet.add vd (vcdesc_fds_set' n' v' vv')
    | Comp c => fun vv =>
      let (vd, vv') := vv in
      FdSet.add (comp_fd (projT1 vd)) (vcdesc_fds_set' n' v' vv')
    | _ => fun vv =>
      let (_, vv') := vv in
      vcdesc_fds_set' n' v' vv'
    end
  end.

Definition vcdesc_fds_set (v : vcdesc) : s[[ v ]] -> FdSet.t :=
  vcdesc_fds_set' (projT1 v) (projT2 v).

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

Inductive InitialState input : kstate -> Prop :=
| C_is : forall s,
           s = init_state_run_cmd IENVD initial_init_state IPROG input ->
           InitialState input {| kcs := init_comps _ s
                               ; ktr := init_ktr _ s
                               ; kst := init_kst _ s
                               ; kfd := FdSet.union
                                      (vcdesc_fds_set _ (init_kst _ s))
                                      (vcdesc_fds_set _ (init_env _ s))
                               |}.

Definition mk_inter_ve_st c m s tr :=
  let cs := kcs s in
  {| kcs := cs
   ; ktr := [KRecv c m :: KSelect cs c :: tr]
   ; kst := kst s
   ; kfd := FdSet.union (vdesc_fds_set _ (pay m)) (kfd s)
   |}.

Inductive ValidExchange (c:comp) (m:msg)
  (input:sdenote_itt (run_cmd_it (projT2 ((HANDLERS (tag m) (comp_type c))))))
  : kstate -> kstate -> Prop :=
| C_ve : forall s tr s',
           let cs := kcs s in
           ktr s = [tr]%inhabited ->
           s' = mk_inter_ve_st c m s tr ->
           let hdlrs := HANDLERS (tag m) (comp_type c) in
           ValidExchange c m input s
             (kstate_run_prog c m (projT1 hdlrs) s'
               (projT2 hdlrs) input).

Definition mk_bogus_st c bmsg s tr :=
  let cs := kcs s in
  {| kcs := cs
   ; ktr := [KBogus c bmsg :: KSelect cs c :: tr]
   ; kst := kst s
   ; kfd := kfd s
   |}.

Inductive BogusExchange (c:comp) (bmsg:bogus_msg)
  : kstate -> kstate -> Prop :=
| C_be : forall s tr,
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  BogusExchange c bmsg s (mk_bogus_st c bmsg s tr).

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall s input,
  InitialState input s ->
  Reach s
| Reach_valid :
  forall c m input s s',
  Reach s ->
  ValidExchange c m input s s' ->
  Reach s'
| Reach_bogus :
  forall s s' c bmsg,
  Reach s ->
  BogusExchange c bmsg s s' ->
  Reach s'.

Definition all_open_set s := FdSet.fold (fun f a => open f * a) s emp.
(*Definition all_open_set s := all_open (FdSet.elements s).*)

(*Definition all_open_set_drop f s := all_open (FdSet.elements (FdSet.remove f s)).*)
Definition all_open_set_drop f s := all_open_set (FdSet.remove f s).

(*Fixpoint all_open_set_drop_all fs s :=
  match fs with
  | nil    => all_open_set s
  | f::fs' => all_open_set_drop_all fs' (FdSet.remove f s)
  end.*)

Definition all_fds_in l s := List.Forall (fun x => FdSet.In (comp_fd x) s) l.

Definition vdesc_fds_subset {envd : vdesc} (env : s[[envd]]) (s : FdSet.t) :=
  FdSet.Subset (vdesc_fds_set envd env) s.

Definition vcdesc_fds_subset {envd : vcdesc} (env : s[[envd]]) (s : FdSet.t) :=
  FdSet.Subset (vcdesc_fds_set envd env) s.
Locate "~~".
Print hprop_unpack.
Definition init_invariant {envd} (s : init_state envd) :=
(*  let fds := init_fds _ s in*)
  let tr := init_ktr _ s in
  tr ~~
  let fds := trace_fds (expand_ktrace tr) in
  all_open_set fds
  * [all_fds_in (init_comps _ s) fds]
  * [vcdesc_fds_subset (init_env _ s) fds]
.

Definition hdlr_invariant {envd} (cc : comp) (cm : msg) (s : hdlr_state envd) :=
  let (kst, env) := s in
  let fds := kfd kst in
  all_open_set fds
  * [FdSet.In (comp_fd cc) fds]
  * [all_fds_in (kcs kst) fds]
  * [vcdesc_fds_subset env fds]
  * [vdesc_fds_subset (pay cm) fds]
.

Definition kstate_inv s : hprop :=
  let fds := kfd s in
  tr :~~ ktr s in
  traced (expand_ktrace tr)
  * all_open_set fds
  * [Reach s]
  * [all_fds_in (kcs s) fds]
  * [vcdesc_fds_subset (kst s) fds]
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
    | Desc num_d => fun _ => emp
    | Desc str_d => fun _ => emp
    | Desc fd_d  => fun f => all_open_set_drop f s (*all_open_payload_drop f env*)
    | Comp ct    => fun _ => emp
    end f
  | CompFd ct bt' => fun f => emp (* TODO *)
  end f.

Definition open_payload_frame_hdlr {CC CMSG ENVD d}
  (s : FdSet.t) (ht : hdlr_term (comp_type CC) (tag CMSG) ENVD d) (f : s[[ d ]])
  : hprop
  :=
  match ht in hdlr_term _ _ _ _d return s[[ _d ]] -> hprop with
  | Base _ bt => fun f => open_payload_frame_base s bt f
  | CComp => fun _ => all_open_set_drop (comp_fd CC) s
  | CConf i => fun f =>
    match svec_ith (projT2 (CCONFD CC)) i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => all_open_set_drop f s
    end f
  | MVar i => fun f =>
    match svec_ith (projT2 (lkup_tag (tag CMSG))) i as _s return s[[ _s ]] -> hprop with
    | num_d => fun _ => emp
    | str_d => fun _ => emp
    | fd_d  => fun f => all_open_set_drop f s
    end f
  | StVar i => fun f =>
    match svec_ith KSTD_DESC i as _s return s[[ _s ]] -> hprop with
    | Desc num_d => fun _ => emp
    | Desc str_d => fun _ => emp
    | Desc fd_d  => fun f => all_open_set_drop f s
    | Comp ct    => fun _ => emp
    end f
  end f.

Definition open_payload_frame_expr {term : vcdesc -> cdesc -> Set} {d envd}
  (opft : term envd d -> s[[d]] -> hprop) (e : expr term envd d) (f : s[[d]])
  : hprop
  :=
  match e in expr _ _ _d return (term _ _d -> s[[_d]] -> hprop) -> s[[_d]] -> hprop with
  | Term _ t => fun opft f => opft t f
  | UnOp _ _ op e1 => fun _ _ => emp
  | BinOp _ _ _ op e1 e2 => fun _ _ => emp
  end opft f.

Definition open_payload_frame_base_expr' {ENVD d} (s : FdSet.t)
  : expr base_term ENVD d -> s[[d]] -> hprop
  := open_payload_frame_expr (open_payload_frame_base s)
.

Definition open_payload_frame_base_expr {ENVD : vcdesc} {d}
  (e : s[[ENVD]]) cs (fds : FdSet.t) (exp : expr base_term ENVD d) (res : s[[d]]) : hprop
  :=
  open_payload_frame_base_expr' fds exp res
  * [all_fds_in cs fds]
  * [vcdesc_fds_subset e fds]
.

Definition open_payload_frame_hdlr_expr' {CC CMSG ENVD d} (s : FdSet.t)
  : expr (hdlr_term (comp_type CC) (tag CMSG)) ENVD d -> s[[d]] -> hprop
  := open_payload_frame_expr (open_payload_frame_hdlr s).

Definition open_payload_frame_hdlr_expr {CC CMSG} {ENVD : vcdesc} {d}
  (e : s[[ENVD]]) cs cm (fds : FdSet.t)
  (exp : expr (hdlr_term (comp_type CC) (tag CMSG)) ENVD d)
  (res : s[[d]]) : hprop
  :=
  open_payload_frame_hdlr_expr' fds exp res
  * [FdSet.In (comp_fd CC) fds]
  * [all_fds_in cs fds]
  * [vcdesc_fds_subset e fds]
  * [vdesc_fds_subset (pay cm) fds]
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
  (* unfold let-bound traces *)
  | [ name := ?value |- _ ] =>
    match type of value with [list KAction]%type =>
      unfold name in *; clear name; simpl in *
    end
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

Ltac get_input :=
  match goal with
  | [ H1 : exists i : ?it1, _ = _,
      H2 : exists i : ?it2, _ = _
    |- exists i : (?it1 * ?it2)%type, _ = _ ]
    => let i1 := fresh "i" in
       let H1' := fresh "H" in
       let i2 := fresh "i" in
       let H2' := fresh "H" in
       destruct H1 as [i1 H1'];
       destruct H2 as [i2 H2'];
       exists (i1, i2)
  | [ H : exists i : ?it, _ = _
    |- exists i : (?it * sdenote_itt (run_cmd_it ?c))%type, _ = _ ]
    => let i := fresh "i" in
       let H' := fresh "H" in
       destruct H as [i H']; exists (i, default_input c)
  | [ H : exists i : ?it, _ = _
    |- exists i : (sdenote_itt (run_cmd_it ?c) * ?it)%type, _ = _ ]
    => let i := fresh "i" in
       let H' := fresh "H" in
       destruct H as [i H']; exists (default_input c, i)
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
  try misc;
  (* only destruct states if it solves the goal, otherwise too much clutter *)
  try solve [now repeat match goal with [ s : init_state _ |- _ ] => destruct s end].

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

Definition trace_send_msg_comps (cps : list comp) (m : msg) : Trace :=
  flat_map (fun c => trace_send_msg (comp_fd c) m) cps.

Lemma hprop_iff_equiv : Equivalence hprop_iff.
Proof.
  sep'.
  apply Symmetric_instance_0.
  apply Transitive_instance_1.
Qed.

Lemma open_proper :
  Morphisms.Proper
  (Morphisms.respectful eq (Morphisms.respectful hprop_iff hprop_iff))
  (fun (f : FdSet.elt) (a : hprop) => open f * a).
Proof.
  unfold Morphisms.Proper. unfold Morphisms.respectful.
  intros. rewrite H. unfold hprop_iff in *. sep'.
Qed.

Lemma open_transpose :
  SetoidList.transpose hprop_iff
  (fun (f : FdSet.elt) (a : hprop) => open f * a).
Proof.
  unfold SetoidList.transpose. intros. unfold hprop_iff. sep'.
Qed.

Theorem all_open_set_packing : forall x s, FdSet.In x s ->
  open x * all_open_set_drop x s <==>
  all_open_set s.
Proof.
  intros. unfold all_open_set, all_open_set_drop.
  apply FdSetProperties.remove_fold_1 with (eqA:=hprop_iff) (x:=x)
    (f:=(fun (f : FdSet.elt) (a : hprop) => open f * a)).
  apply hprop_iff_equiv. apply open_proper. apply open_transpose.
  assumption.
Qed.
(*
  setoid_replace (all_open_set' (FdSet.add c_fd fds)) with
    (open c_fd * all_open_set' fds).
(*  apply himp_trans with (Q := open x * all_open_drop (FdSet.elements s) x).*)
  apply unpack_all_open.
  apply FdSet.elements_spec1 in H.
  apply SetoidList.InA_alt in H.
  destruct H as [y [EQ IN] ]. now inversion_clear EQ.
(*  sep'.
  induction s using FdSetProperties.set_induction.
    specialize (H0 x). contradiction.
    
    remember H1 as H1'. clear HeqH1'.
    specialize (H1' x). destruct H1'.
    specialize (H2 H). destruct H2.
    unfold FdSetProperties.Add in H1'.

  (* TODO: this is tedious *)
Admitted.*)
Qed.*)

(*Theorem all_open_set_pack : forall x s, FdSet.In x s ->
  open x * all_open_set_drop x s ==>
  all_open_set s.
Proof.
  (* TODO: Just copy on all_open_set_unpack *)
  intros. unfold all_open_set, all_open_set_drop.
(*  apply himp_trans with (Q := open x * all_open_drop (FdSet.elements s) x).*)
  apply repack_all_open.
  apply FdSet.elements_spec1 in H.
  apply SetoidList.InA_alt in H.
  destruct H as [y [EQ IN] ]. now inversion_clear EQ.
Qed.*)

Definition send_msg_comps :
  forall (m : msg) (cps : list comp) (fds : FdSet.t)
         (tr : [Trace]),
  STsep (tr ~~ all_open_set fds * [all_fds_in cps fds] * traced tr)
        (fun _ : unit => tr ~~
          all_open_set fds * [all_fds_in cps fds] *
          traced ((trace_send_msg_comps cps m)  ++ tr)).
Proof.
  intros; refine (
    Fix2
      (fun (cps : list comp) (tr : [Trace]) =>
         (tr ~~ all_open_set fds * [all_fds_in cps fds] * traced tr))
      (fun cps tr (_ : unit) => tr ~~
          all_open_set fds * [all_fds_in cps fds] *
          traced ((trace_send_msg_comps cps m)  ++ tr))
      (fun self cps tr =>
        match cps with
        | nil => {{ Return tt }}
        | c::cps' =>
          self cps' tr <@> [all_fds_in (c::cps') fds];;
          send_msg (comp_fd c) m (tr ~~~ (trace_send_msg_comps cps' m)  ++ tr)
          <@> [all_fds_in (c::cps') fds] * all_open_set_drop (comp_fd c) fds;;
          {{ Return tt }}
        end
      )
    cps tr
  ); sep''.
  inversion H; auto.
  apply all_open_set_packing. now inversion H0.
  rewrite app_assoc; sep''.
  apply all_open_set_packing. now inversion H.
Qed.

Lemma expand_ktrace_dist : forall tr1 tr2,
  expand_ktrace (tr1 ++ tr2) = expand_ktrace tr1 ++ expand_ktrace tr2.
Proof.
  intro tr1.
  induction tr1; simpl.
  reflexivity.

  intro tr2.
  rewrite IHtr1.
  apply app_assoc.
Qed.

Lemma expand_ktrace_trace_send_msg_comps : forall cps m,
  trace_send_msg_comps cps m = expand_ktrace (ktrace_send_msgs cps m).
Proof.
  intros cps m.
  induction cps; simpl.
  reflexivity.

  rewrite IHcps.
  reflexivity.
Qed.

Lemma vcdesc_fds_subset_rest :
  forall fds RESTSIZE
         (PAY0: cdesc) (PAYREST: vcdesc' RESTSIZE) (e0: s[[PAY0]]) (erest: s[[PAYREST]]),
  vcdesc_fds_subset (envd := existT vcdesc' (S RESTSIZE) (PAY0, PAYREST)) (e0, erest) fds ->
  vcdesc_fds_subset (envd := existT vcdesc' _ PAYREST) erest fds.
Proof.
  intros until 0. intros SUB.
  unfold vcdesc_fds_subset, vcdesc_fds_set in *.
  simpl. simpl in SUB.
  destruct PAY0 as []_eqn.
  destruct d as []_eqn; try easy.
  intros ? IN. apply SUB. apply FdSet.add_spec. now right.
  intros ? IN. apply SUB. apply FdSet.add_spec. now right.
Qed.

Lemma ridiculous_lemma: forall
  (c: COMPT)
  (ENVD_SIZE: nat)
  (PAYREST: vcdesc' ENVD_SIZE)
  (erest: shvec sdenote_cdesc PAYREST)
  (i: fin ENVD_SIZE)
  (EQ: svec_ith PAYREST i = Comp c),
  eval_base_term (envd:=existT _ ENVD_SIZE PAYREST) erest
    match EQ in _ = __vi return base_term (existT vcdesc' ENVD_SIZE PAYREST) __vi with
    | Logic.eq_refl => Var (existT vcdesc' ENVD_SIZE PAYREST) i
    end
  =
  match EQ in _ = __vi return s[[__vi]] with
  | Logic.eq_refl =>
    eval_base_term
      (envd:=existT _ ENVD_SIZE PAYREST)
      erest (Var (existT vcdesc' ENVD_SIZE PAYREST) i)
  end.
Proof.
  intros. dependent inversion EQ. reflexivity.
Qed.

Lemma ridiculous_lemma2: forall
  (c: COMPT)
  (ENVD_SIZE: nat)
  PAY0
  (e0: s[[PAY0]])
  (PAYREST: vcdesc' ENVD_SIZE)
  (erest: shvec sdenote_cdesc PAYREST)
  (i: fin ENVD_SIZE)
  (EQ: svec_ith PAYREST i = Comp c),
  eval_base_term (envd:=existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) (e0, erest)
    match EQ in _ = __vi return
      base_term (existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) __vi
    with
    | Logic.eq_refl => Var (existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) (Some i)
    end
  =
  match EQ in _ = __vi return s[[__vi]] with
  | Logic.eq_refl =>
    eval_base_term
      (envd:=existT _ (S ENVD_SIZE) (PAY0, PAYREST))
      (e0, erest) (Var (existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) (Some i))
  end.
Proof.
  intros. dependent inversion EQ. reflexivity.
Qed.

Lemma send_lemma: forall envd (e : s[[envd]]) fds i,
  vcdesc_fds_subset e fds ->
  match svec_ith (projT2 envd) i as __d return (base_term envd __d -> Prop) with
  | Desc d => fun _ => True
  | Comp c => fun b => FdSet.In (comp_fd (projT1 (eval_base_term e b))) fds
  end (Var envd i).
Proof.
  intros [ENVD_SIZE ENVD_PAY]. revert ENVD_PAY. induction ENVD_SIZE.
  intros. now exfalso.
  intros ENVD_PAY e fds i SUB.
  simpl in ENVD_PAY. destruct ENVD_PAY as [PAY0 PAYREST].
  simpl in i. destruct i as [i|].
  simpl in e. unfold sdenote_vcdesc, sdenote_vcdesc' in e.
  simpl in e. destruct e as [e0 erest].
  specialize (IHENVD_SIZE PAYREST erest fds i (vcdesc_fds_subset_rest _ _ _ _ _ _ SUB)).
  simpl in *. revert IHENVD_SIZE.

  pose (shvec_ith sdenote_cdesc PAYREST erest i) as v1.
  pose (shvec_ith (n:=S ENVD_SIZE) sdenote_cdesc (PAY0, PAYREST) (e0, erest) (Some i)) as v2.

refine (
match svec_ith PAYREST i as _vi return
   forall (EQ: (svec_ith (projT2 (existT vcdesc' ENVD_SIZE PAYREST)) i) = _vi),
   match
     _vi as __d
     return (base_term (existT vcdesc' ENVD_SIZE PAYREST) __d -> Prop)
   with
   | Desc d => fun _ => True
   | Comp c => fun b=>
       FdSet.In
         (comp_fd (projT1 (eval_base_term (envd:=existT _ ENVD_SIZE PAYREST) erest b)))
         fds
   end
     match EQ in _ = __vi return base_term _ __vi with Logic.eq_refl =>
       Var (existT vcdesc' ENVD_SIZE PAYREST) i
     end
   ->
   match
     _vi as __d
     return
       (base_term (existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) __d -> Prop)
   with
   | Desc d => fun _ => True
   | Comp c => fun b =>
       FdSet.In
         (comp_fd (projT1 (eval_base_term (envd:=existT _ (S ENVD_SIZE) (PAY0, PAYREST)) (e0, erest) b)))
         fds
   end
     match EQ in _ = __vi return base_term _ __vi with Logic.eq_refl =>
       Var (existT vcdesc' (S ENVD_SIZE) (PAY0, PAYREST)) (Some i)
     end
with
| Desc d => _
| Comp c => _
end (Logic.eq_refl _)
).
easy.
intros EQ. simpl in EQ.
rewrite ridiculous_lemma. rewrite ridiculous_lemma2.
now simpl.

simpl. destruct PAY0 as []_eqn.
easy.
simpl in *.
unfold sdenote_vcdesc in e. simpl in *. destruct e as [e0 e].
apply SUB. unfold vcdesc_fds_set. simpl. apply FdSet.add_spec. now left.
Qed.

(*Lemma trace_send_fds_empty : forall f m,
  FdSet.Empty (trace_fds (trace_send_msg f m)).
Proof.
  intros f m.
  unfold trace_send_msg. unfold trace_payload_send.
  unfold trace_payload. unfold trace_payload'.
  destruct m as [t p]. simpl. destruct (lkup_tag t) as [n pd]. simpl.
  induction n.
    destruct (num_of_fin t).
    Local Transparent SendNum. simpl.
Print FdSet.
    apply FdSet.is_empty_spec.
    apply FdSetProperties.empty_union_2.*)

Lemma trace_fds_dist : forall tr1 tr2,
  FdSet.Equal (FdSet.union (trace_fds tr1) (trace_fds tr2))
              (trace_fds (tr1 ++ tr2)).
Proof.
  intros tr1 tr2.
  induction tr1.
    simpl. apply FdSetProperties.empty_union_1.
    apply FdSet.empty_spec.

    simpl. setoid_rewrite FdSetProperties.union_assoc.
    setoid_rewrite IHtr1. apply FdSetProperties.equal_refl.
Qed.

Lemma trace_fds_comm : forall tr1 tr2,
  FdSet.Equal (trace_fds (tr1 ++ tr2)) (trace_fds (tr2 ++ tr1)).
Proof.
  intros tr1 tr2.
  setoid_rewrite <- trace_fds_dist.

  setoid_rewrite FdSetProperties.union_sym at 1.
  apply FdSetProperties.equal_refl.
Qed.

Lemma trace_send_fds_empty : forall f m,
  FdSet.Equal (trace_fds (trace_send_msg f m)) FdSet.empty.
Proof.
  Local Transparent SendNum SendStr num_of_nat.
  intros f m.
  unfold trace_send_msg. unfold trace_payload_send.
  unfold trace_payload. unfold trace_payload'.
  destruct m as [t p]. simpl. destruct (lkup_tag t) as [n pd]. simpl.
  setoid_rewrite <- trace_fds_dist.
  destruct (num_of_fin t). simpl.
  repeat setoid_rewrite FdSetProperties.empty_union_1.
  apply FdSetProperties.equal_refl. apply FdSet.empty_spec.
  induction n.
    simpl. apply FdSet.empty_spec.

    unfold trace_send. simpl in *. destruct pd. simpl in *.
    unfold sdenote_vdesc in *. simpl in *. destruct p. simpl in *.
    destruct d; simpl in *; repeat rewrite app_ass;
    setoid_rewrite trace_fds_comm; destruct s; simpl;
    repeat setoid_rewrite FdSetProperties.empty_union_1; (apply IHn ||
        apply FdSet.empty_spec).
Qed.

Lemma trace_send_fds : forall f m tr,
  all_open_set (trace_fds (trace_send_msg f m ++ tr)) <==> all_open_set (trace_fds tr).
Proof.
  intros f m tr.
  unfold all_open_set.
  apply FdSetProperties.fold_equal.
  apply hprop_iff_equiv. apply open_proper. apply open_transpose.
  setoid_rewrite <- trace_fds_dist.
  setoid_rewrite trace_send_fds_empty.
  apply FdSetProperties.empty_union_1.
  apply FdSet.empty_spec.
Qed.

Lemma trace_fds_app_subset : forall tr1 tr2,
  FdSet.Subset (trace_fds tr1)
  (trace_fds (tr2 ++ tr1)).
Proof.
  intros tr1 tr2.
  setoid_rewrite <- trace_fds_dist.
  apply FdSetProperties.union_subset_2.
Qed.

Definition run_init_cmd :
  forall (envd : vcdesc) (s : init_state envd)
         (c : cmd base_term envd),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr) *
          [exists i, s' = init_state_run_cmd envd s c i]).
Proof.
  intros envd sinit cinit;
  refine (Fix3
    (fun envd c s => tr :~~ init_ktr envd s in
      init_invariant s * traced (expand_ktrace tr))
    (fun envd c s (s' : init_state envd) => tr :~~ init_ktr envd s' in
      init_invariant s' * traced (expand_ktrace tr) *
      [exists i, s' = init_state_run_cmd envd s c i])
    (fun self envd0 c0 s0 => _) envd cinit sinit
  ).
  clear cinit sinit envd HANDLERS IPROG IENVD.
  refine (
    match c0 as _c0 in cmd _ _envd0 return
      forall (_s0 : init_state _envd0),
         STsep
           (tr0 :~~ init_ktr _envd0 _s0 in
               init_invariant _s0 * traced (expand_ktrace tr0))
         (fun s' : init_state _envd0 => tr' :~~ init_ktr _envd0 s' in
           init_invariant s' * traced (expand_ktrace tr') *
           [exists i, s' = init_state_run_cmd _envd0 _s0 _c0 i])
    with

    | Nop _ => fun s => {{ Return s }}

    | Seq envd c1 c2 => fun s =>
      let case := "Seq envd c1 c2"%string in _

    | Ite envd cond c1 c2 => fun s =>
      let case := "Ite envd cond c1 c2"%string in _

    | Send _ ct ce t me => fun s =>
      let case := "Send _ ct ce t me"%string in _

(*    | SendAll _ cp t me => fun s =>
      let case := "SendAll _ cp t me"%string in _*)

    | Spawn _ ct cfg i EQ => fun s =>
      let case := "Spawn _ ct cfg i EQ"%string in _

    | Call _ ce argse i EQ => fun s =>
      let case := "Call _ ce argse i EQ"%string in _

    | StUpd _ i ve => fun s =>
      let case := "StUpd _ i ve"%string in _

    | CompLkup envd cp c1 c2 => fun s =>
      let case := "CompLkup envd cp c1 c2"%string in _

    end s0
  ); sep''.

(* Seq *)
refine (
  s1 <- self envd c1 s;
  s2 <- self envd c2 s1
    <@> [exists i, s1 = init_state_run_cmd envd s c1 i];
  {{ Return s2 }}
); sep''.
get_input.
simpl.
rewrite <- H.
assumption.

(* Ite *)
refine (
  if num_eq (eval_base_expr (init_env _ s) cond) FALSE
  then s' <- self envd c2 s; {{ Return s' }}
  else s' <- self envd c1 s; {{ Return s' }}
); sep''.
destruct (num_eq (eval_base_expr (init_env envd s) cond) FALSE).
get_input. auto.
contradiction.
destruct (num_eq (eval_base_expr (init_env envd s) cond) FALSE).
contradiction.
get_input. auto.

(* Send *)
destruct s as [cs tr e st fds]_eqn; simpl.
refine (
  let c := projT1 (eval_base_expr e ce) in
  let m := eval_base_payload_expr _ e _ me in
  let msg := Build_msg t m in
  send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ let fds := trace_fds (expand_ktrace tr) in
         all_open_set_drop (comp_fd c) fds
(*    * [In c cs]*)
         * [all_fds_in cs fds]
         * [vcdesc_fds_subset e fds]);;
  let tr := tr ~~~ KSend c msg :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := e
             ; init_kst   := st
             ; init_fds   := fds
             |}
  }}
); sep''.
etransitivity.
apply all_open_set_packing with (x := comp_fd c).
unfold c. clear c.
dependent inversion_clear ce with (
  fun _d _ce =>
  match _d as __d return expr _ _ __d -> _ with
  | Comp _ => fun ce =>
    FdSet.In (comp_fd (projT1 (eval_base_expr e ce))) (trace_fds (expand_ktrace x))
  | _      => fun _ => False
  end _ce
); simpl.
dependent inversion_clear b with (
  fun _d _b =>
  match _d as __d return base_term _ __d -> Prop with
  | Comp _ => fun b =>
    FdSet.In (comp_fd (projT1 (eval_base_term e b))) (trace_fds (expand_ktrace x))
  | _      => fun _ => True
  end _b
).
now apply send_lemma.
inversion u.
inversion b.
sep''.
rewrite trace_send_fds.
apply all_open_set_packing.
unfold c. clear c.
dependent inversion_clear ce with (
  fun _d _ce =>
  match _d as __d return expr _ _ __d -> _ with
  | Comp _ => fun ce =>
    FdSet.In (comp_fd (projT1 (eval_base_expr e ce))) (trace_fds (expand_ktrace x0))
  | _      => fun _ => False
  end _ce
); simpl.
dependent inversion_clear b with (
  fun _d _b =>
  match _d as __d return base_term _ __d -> Prop with
  | Comp _ => fun b =>
    FdSet.In (comp_fd (projT1 (eval_base_term e b))) (trace_fds (expand_ktrace x0))
  | _      => fun _ => True
  end _b
).
now apply send_lemma.
inversion u.
inversion b.
eapply FdSetProperties.subset_trans; eauto.
apply trace_fds_app_subset.
unfold all_fds_in in *.
rewrite Forall_forall in *. intros.
eapply FdSetProperties.in_subset; eauto.
apply trace_fds_app_subset.

(* SendAll *)
(*destruct s as [cs tr e st fds]_eqn; simpl.
refine (
  let m := eval_base_payload_expr _ e _ me in
  let comps := filter_comps base_term (fun d envd e => @eval_base_term _ _ e) _ _ cp cs in
  let msg := Build_msg t m in
  send_msg_comps msg comps fds (tr ~~~ expand_ktrace tr)
    <@> [all_fds_in cs fds] * [vcdesc_fds_subset e fds];;

  let tr := tr ~~~ ktrace_send_msgs comps msg ++ tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := e
             ; init_kst   := st
             ; init_fds   := fds
             |}
  }}
); sep''.
admit.
admit.
exists tt. admit.*)

(* Spawn *)
destruct s as [cs tr e st fds]_eqn; simpl.
refine (
  let c_cmd := compd_cmd (COMPS ct) in
  let c_args := compd_args (COMPS ct) in
  c_fd <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
      <@> init_invariant s;

  let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  let tr := tr ~~~ KExec c_cmd c_args c :: tr in
  {{ Return {| init_comps := c :: cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e (existT _ c (Logic.eq_refl ct))
             ; init_kst   := st
             ; init_fds   := FdSet.add c_fd fds
             |}
  }}
); sep''.
unfold all_open_set.
rewrite hstar_comm.
replace (open c_fd *
  FdSet.fold (fun (f : FdSet.elt) (a : hprop) => open f * a)
    (trace_fds (expand_ktrace x3)) emp) with
(FdSet.fold (fun (f : FdSet.elt) (a : hprop) => open f * a)
    (FdSet.singleton c_fd)
    (FdSet.fold (fun (f : FdSet.elt) (a : hprop) => open f * a)
       (trace_fds (expand_ktrace x3)) emp)).
rewrite FdSetProperties.fold_union with (eqA:=hprop_iff)
  (f:=(fun (f : FdSet.elt) (a : hprop) => open f * a))
  (s:=FdSet.singleton c_fd) (s':=(trace_fds (expand_ktrace x3)))
  (i:=emp).
sep''.
apply hprop_iff_equiv. apply open_proper. apply open_transpose.
intros. unfold not. intros. destruct H2. rewrite FdSet.singleton_spec in H2.

Check FdSet.in_spec.

(*Lemma open_lists : forall l1 l2,
  SetoidList.equivlistA eq l1 l2 ->
  all_open l1 ==> all_open l2.
Proof.
  intros l1.
  induction l1.
    intros.
    assert (l2 = nil). 
      destruct l2; auto.
      unfold SetoidList.equivlistA in H.
      specialize (H f). destruct H.
      assert (SetoidList.InA eq f (f:: l2)) by auto.
      apply H0 in H1. inversion H1.

    rewrite H0. auto.

    intros.
    induction l2.
      unfold SetoidList.equivlistA in H.
      specialize (H a).
      assert (SetoidList.InA eq a (a:: l1)) by auto.
      apply H in H0. inversion H0.
*)
      
Lemma hprop_iff_equiv : Equivalence hprop_iff.
Proof.
  sep'.
  apply Symmetric_instance_0.
  apply Transitive_instance_1.
Qed.

Lemma open_proper :
  Morphisms.Proper
  (Morphisms.respectful eq (Morphisms.respectful hprop_iff hprop_iff))
  (fun (f : FdSet.elt) (a : hprop) => open f * a).
Proof.
  unfold Morphisms.Proper. unfold Morphisms.respectful.
  intros. rewrite H. unfold hprop_iff in *. sep'.
Qed.

Lemma open_transpose :
  SetoidList.transpose hprop_iff
  (fun (f : FdSet.elt) (a : hprop) => open f * a).
Proof.
  unfold SetoidList.transpose. intros. unfold hprop_iff. sep'.
Qed.
  
Definition all_open_set' (s : FdSet.t) : hprop :=
  FdSet.fold (fun f a => open f * a) s emp.
Lemma open_sets_equal : forall s s',
  FdSet.Equal s s' ->
  all_open_set' s ==> all_open_set' s' /\ all_open_set' s' ==> all_open_set' s.
Proof.
  intros s s' Heq. unfold all_open_set'.
  apply FdSetProperties.fold_equal with (eqA:=hprop_iff).
  
  apply hprop_iff_equiv.

  apply open_proper.

  apply open_transpose.

  auto.
Qed.

Lemma test : forall c_fd fds,
  all_open_set' (FdSet.add c_fd fds) <==> open c_fd * all_open_set' fds.
Proof.
  intros. unfold all_open_set'.
  apply FdSetProperties.fold_add with (eqA:=hprop_iff) (x:=c_fd).
  apply hprop_iff_equiv. apply open_proper. apply open_transpose.

  setoid_replace (all_open_set' (FdSet.add c_fd fds)) with
    (open c_fd * all_open_set' fds).
  sep'.
  

Lemma open_sets_equal : forall s s',
  FdSet.Equal s s' ->
  all_open_set s ==> all_open_set s'.
Proof.
  intros s.
  induction s using FdSetProperties.set_induction.
    intros s' Heq.
    assert (FdSet.Empty s').
      unfold FdSet.Empty in *. intro e.
      specialize (H e). unfold FdSet.Equal in Heq.
      specialize (Heq e). intuition.
    unfold all_open_set. apply FdSetProperties.elements_Empty in H.
    apply FdSetProperties.elements_Empty in H0. rewrite H. rewrite H0.
    auto.

    intros.
    


assert (open c_fd * all_open_set_drop c_fd (FdSet.add c_fd fds) ==> all_open_set (FdSet.add c_fd fds)).
  apply all_open_set_pack. rewrite FdSet.add_spec. left. auto.
Definition all_open_set' (s : FdSet.t) : hprop :=
  FdSet.fold (fun f a => open f * a) s emp.
Lemma all_open_set_add : forall f fds,
  open f * all_open_set' fds ==> all_open_set' (FdSet.add f fds).
Proof.
  intros f fds. unfold all_open_set'.
  apply FdSetProperties.fold_rec.
    intros.
    simpl. 

    
unfold all_open_set.
unfold all_open.
admit.
admit.
constructor.
  rewrite FdSet.add_spec. auto.

  rewrite Forall_forall. unfold all_fds_in in H. rewrite Forall_forall in H.
  intros. specialize (H x H1). eapply FdSetProperties.in_subset. eapply H.
  eapply FdSetProperties.subset_add_2. apply FdSetProperties.subset_refl.
exists c_fd. sep''.

(* Call *)
destruct s as [cs tr e st fds]_eqn; simpl.
refine (
  let c := eval_base_expr e ce in
  let args := map (eval_base_expr e) argse in
  f <- call c args (tr ~~~ expand_ktrace tr)
   <@> init_invariant s;

  let tr := tr ~~~ KCall c args f :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e f
             ; init_kst   := st
             ; init_fds   := FdSet.add f fds
             |}
  }}
); sep''.
admit.
admit.
admit.
exists f. sep''.

(* StUpd *)
destruct s as [cs tr e st fds]_eqn; simpl.
refine (
  let v := eval_base_expr e ve in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := e
             ; init_kst   := shvec_replace_ith _ _ st i v
             ; init_fds   := fds
             |}
  }}
); sep''.

(* CompLkup *)
destruct s as [cs tr e st fds]_eqn; simpl.
pose (ocdp := find_comp base_term (fun d envd e => eval_base_term e) envd e cp cs).
destruct ocdp as [ cdp | ]_eqn.
(*Component found*)
refine (
  let c := projT1 cdp in
  let d := Comp (comp_pat_type _ _ cp) in
  let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
  let s' := Build_init_state new_envd cs tr
    (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
      (existT _ c (projT2 cdp)) (projT2 envd) e)
  st fds in
  s'' <- self new_envd c1 s';
  {{ Return {| init_comps := init_comps _ s''
             ; init_ktr   := init_ktr _ s''
             ; init_env   := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (init_env _ s'')
             ; init_kst   := init_kst _ s''
             ; init_fds   := init_fds _ s''
             |}
  }}
); sep''.
admit.
admit.
get_input. admit.
admit.
admit.
(*Component not found*)
refine (
  s' <- self envd c2 s;
  {{ Return s' }}
); sep''.
rewrite Heqo.
get_input. auto.
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
    s' <- run_init_cmd _ s IPROG;
    {{ Return {| kcs := init_comps _ s'
               ; ktr := init_ktr _ s'
               ; kst := init_kst _ s'
               ; kfd := FdSet.union
                          (vcdesc_fds_set KSTD (init_kst IENVD s'))
                          (vcdesc_fds_set IENVD (init_env IENVD s'))
               |}
     }}
  ); sep''.
  admit.
  admit.
  admit.
  admit.
  match goal with
  | [ H : exists i : _, _ = _ |- _ ]
    => let i := fresh "i" in
       let Hin := fresh "Hin" in
       destruct H as [i Hin];
       eapply Reach_init with (input:=i);
       eauto
  end.
  econstructor; eauto.
  admit.
  admit.
Qed.

Definition run_hdlr_cmd :
  forall (cc : comp) (cm : msg) (envd : vcdesc) (s : hdlr_state envd)
         (c : cmd (hdlr_term (comp_type cc) (tag cm)) envd),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cc cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cc cm s' * traced (expand_ktrace tr)
          * [exists i, s' = hdlr_state_run_cmd cc cm envd s c i]).
Proof.
  intros cc cm envd sinit cinit;
  refine (Fix3
    (fun envd c s => tr :~~ ktr (hdlr_kst envd s) in
      hdlr_invariant cc cm s * traced (expand_ktrace tr))
    (fun envd c s (s' : hdlr_state envd) => tr :~~ ktr (hdlr_kst envd s') in
      hdlr_invariant cc cm s' * traced (expand_ktrace tr)
      * [exists i, s' = hdlr_state_run_cmd cc cm envd s c i]
    )
    (fun self envd0 c s0 => _) envd cinit sinit
  ).
  clear cinit sinit envd HANDLERS IPROG IENVD.

  refine (
  (* /!\ We lose track of the let-open equalities if existentials remain,
         make sure that Coq can infer _all_ the underscores. *)
  match c as _c in cmd _ _envd return
    forall (s : hdlr_state _envd),
    STsep
     (tr :~~ ktr (hdlr_kst _ s) in
         hdlr_invariant cc cm s * traced (expand_ktrace tr))
     (fun s' : hdlr_state _envd =>
      tr :~~ ktr (hdlr_kst _envd s') in
         hdlr_invariant cc cm s' * traced (expand_ktrace tr)
         * [exists i, s' = hdlr_state_run_cmd cc cm _envd s _c i])
  with

  | Nop _ => fun s => {{ Return s }}

  | Seq _ c1 c2 => fun s =>
    let case := "Seq _ c1 c2"%string in _

  | Ite _ cond c1 c2 => fun s =>
    let case := "Ite _ cond c1 c2"%string in _

  | Send _ ct ce t me => fun s =>
    let case := "Send _ ct ce t me"%string in _

  | SendAll _ cp t me => fun s =>
    let case := "SendAll _ cp t me"%string in _

  | Spawn _ ct cfg i EQ => fun s =>
    let case := "Spawn _ ct cfg i EQ"%string in _

  | Call _ ce argse i EQ => fun s =>
    let case := "Call _ ce argse i EQ"%string in _

  | StUpd _ i ve => fun s =>
    let case := "StUpd _ i ve"%string in _

  | CompLkup _ cp c1 c2 => fun s =>
    let case := "CompLkup _ cp c1 c2"%string in _

  end s0
  ); sep''; try subst v; sep'; simpl in *.

(* Seq *)
refine (
  s1 <- self _ c1 s;
  s2 <- self _ c2 s1
    <@> [exists i, s1 = hdlr_state_run_cmd _ _ envd s c1 i];
  {{ Return s2 }}
); sep''.
get_input.
simpl.
rewrite <- H.
assumption.

(* Ite *)
destruct s as [ ks env]_eqn.
refine (
  if num_eq (eval_hdlr_expr _ _ (kst (hdlr_kst _ s)) (hdlr_env _ s) cond) FALSE
  then s' <- self _ c2 s; {{ Return s' }}
  else s' <- self _ c1 s; {{ Return s' }}
); sep''.
destruct (num_eq (eval_hdlr_expr cc cm (kst ks) env cond) FALSE).
get_input. auto.
contradiction.
destruct (num_eq (eval_hdlr_expr cc cm (kst ks) env cond) FALSE).
contradiction.
get_input. auto.

(*Send*)
destruct s as [ [cs tr st fds] env]_eqn.
refine (
  let c := projT1 (eval_hdlr_expr cc cm st env ce) in
  let m := eval_hdlr_payload_expr cc cm st _ env _ me in
  let msg := (Build_msg t m) in
  send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
    <@> [In c cs]
      * [all_fds_in cs fds]
      * [vcdesc_fds_subset env fds]
      * [vdesc_fds_subset (pay cm) fds];;

  {{ Return {| hdlr_kst :=
               {| kcs := cs
                ; ktr := tr ~~~ KSend c msg :: tr
                ; kst := st
                ; kfd := fds
                |}
               ; hdlr_env := env
               |}
  }}
); sep''.
admit.
admit.
admit.
admit.

(*SendAll*)
destruct s as [ [cs tr st fds] env]_eqn.
refine (
  let m := eval_hdlr_payload_expr cc cm st envd env _ me in
  let comps := filter_comps (hdlr_term _ (tag cm))
    (fun d envd e t => @eval_hdlr_term _ _ st d envd t e) _ _ cp cs in
  let msg := Build_msg t m in
  send_msg_comps msg comps fds (tr ~~~ expand_ktrace tr)
    <@> [FdSet.In (comp_fd cc) fds]
      * [all_fds_in cs fds]
      * [vcdesc_fds_subset env fds]
      * [vdesc_fds_subset (pay cm) fds];;

  let tr := tr ~~~ ktrace_send_msgs comps msg ++ tr in
  {{ Return {| hdlr_kst := {| kcs := cs ; ktr := tr ; kst := st ; kfd := fds |}
             ; hdlr_env := env
             |}
  }}
); sep''.
admit.
admit.
exists tt. admit.

(*Spawn*)
destruct s as [ [cs tr st fds] env]_eqn.
refine (
  let c_cmd := compd_cmd (COMPS ct) in
  let c_args := compd_args (COMPS ct) in
  c_fd <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s;

  let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  let tr := tr ~~~ KExec c_cmd c_args c :: tr in
  {{ Return {| hdlr_kst := {| kcs := c :: cs
                            ; ktr := tr
                            ; kst := st
                            ; kfd := FdSet.add c_fd fds |}
             ; hdlr_env := shvec_replace_cast EQ env (existT _ c (Logic.eq_refl ct))
             |}
  }}
); sep''.
admit.
admit.
admit.
admit.
admit.
exists c_fd.
unfold c0. repeat f_equal; auto.

(*Call*)
destruct s as [ [cs tr st fds] env]_eqn.
refine (
  let c := eval_hdlr_expr _ _ _ _ ce in
  let args := map (eval_hdlr_expr _ _ _ _) argse in
  f <- call c args (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s;

  let tr := tr ~~~ KCall c args f :: tr in
  {{ Return {| hdlr_kst := {| kcs := cs
                            ; ktr := tr
                            ; kst := st
                            ; kfd := FdSet.add f fds |}
             ; hdlr_env := shvec_replace_cast EQ env f
             |}
  }}
); sep''.
admit.
admit.
admit.
admit.
admit.
exists f. admit.

(*StUpd*)
destruct s as [ [cs tr st fds] env]_eqn.
refine (
  let v := eval_hdlr_expr cc cm st env ve in
  {{ Return {| hdlr_kst := {| kcs := cs
                            ; ktr := tr
                            ; kst := shvec_replace_ith _ _ st i v
                            ; kfd := fds
                            |}
             ; hdlr_env := env
             |}
  }}
); sep''.

(*CompLkup*)
destruct s as [ [cs tr st fds] env]_eqn.
pose (ocdp := find_comp (hdlr_term (comp_type cc) (tag cm))
                        (fun d envd e t => @eval_hdlr_term _ _ st d envd t e) envd env cp cs).
destruct ocdp as [ cdp | ]_eqn.
(*Component found*)
refine (
  let c := projT1 cdp in
  let d := Comp (comp_pat_type _ _ cp) in
  let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
  let s' := Build_hdlr_state new_envd {| kcs := cs
                                       ; ktr := tr
                                       ; kst := st
                                       ; kfd := fds
                                       |}
                     (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                       (existT _ c (projT2 cdp)) (projT2 envd) env) in
  s'' <- self new_envd c1 s';
  let (ks'', new_env) := s'' in
  {{ Return {| hdlr_kst :=
                {| kcs := kcs ks''
                 ; ktr := ktr ks''
                 ; kst := kst ks''
                 ; kfd := kfd ks''
                 |}
             ; hdlr_env := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) new_env
             |}
  }}
); sep''.
subst s'. simpl. admit.
subst v. destruct s''. simpl. sep''.
admit.
admit.
admit.
admit.
admit.
get_input.
admit.

(*Component not found*)
refine (
  s' <- self envd c2 s;
  {{ Return s' }}
); sep''.
unfold CT. unfold CTAG.
rewrite Heqo. get_input. auto.
Qed.

Theorem all_open_unconcat : forall a b,
  all_open (a ++ b) ==> all_open a * all_open b.
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
Qed.

Axiom in_devnull_default_payload: forall henv l,
  vcdesc_fds_in (devnull :: l) henv (default_cpayload henv).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intro s; destruct s as [cs tr st fds]_eqn; refine (
    c <- select_comp cs
    (tr ~~~ expand_ktrace tr)
    <@> all_open_set fds * [Reach s] * [all_fds_in cs fds] * [vcdesc_fds_subset st fds];

    let tr := tr ~~~ KSelect cs c :: tr in
    mm <- recv_msg (comp_fd c)
    (tr ~~~ expand_ktrace tr)
    <@> all_open_set_drop (comp_fd c) fds * [FdSet.In (comp_fd c) fds] * [Reach s]
    * [all_fds_in cs fds] * [vcdesc_fds_subset st fds];

    match mm with
    | inl m =>
      let tr := tr ~~~ KRecv c m :: tr in
      let hdlrs := HANDLERS (tag m) (comp_type c) in
      let henv  := projT1 hdlrs in
      let hprog := projT2 hdlrs in
      let s' := {| hdlr_kst := {| kcs := cs
                                ; ktr := tr
                                ; kst := st
                                ; kfd := FdSet.union (vdesc_fds_set _ (pay m)) fds |}
                 ; hdlr_env := default_cpayload henv
                 |}
      in
      s'' <- run_hdlr_cmd c m henv s' hprog
      <@> [Reach s];
      {{ Return (hdlr_kst _ s'') }}
    | inr m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{ Return {|kcs := cs; ktr := tr; kst := st; kfd := fds |} }}
    end

  ); sep''; try subst v; sep'; simpl in *.

  apply himp_comm_conc.
  apply all_open_set_unpack; auto.
  admit.
  admit. (* easy. Same as the previous one. *)

  admit. (* combine 'In c (proj_fds cs)' and 'all_fds_in cs fds' *)

  admit.
  admit.
  admit.
  apply FdSet.union_spec; auto.
  destruct s'' as [kst'' env'']; destruct kst''; sep''.
  admit. (* TODO *)
  admit.
  match goal with
  | [ H : exists i : _, _ = _ |- _ ]
    => let i := fresh "i" in
       let Hin := fresh "Hin" in
       destruct H as [i Hin];
       apply Reach_valid with (s:=s) (c:=c) (m:=m)
         (input:=i);
       auto
  end.
  subst s''.
  subst s.
  apply C_ve with (tr:=x1); auto.
  rewrite H1.
  auto.
  apply all_open_set_pack; auto.

  eapply Reach_bogus; eauto.
  eapply C_be; eauto.
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
