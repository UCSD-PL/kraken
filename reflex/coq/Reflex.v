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

Definition vcdesc' n : Set := svec cdesc n.

Definition sdenote_vcdesc' n (pt : vcdesc' n) : Set :=
  shvec sdenote_cdesc pt.

Instance SDenoted_vcdesc' {n} : SDenoted (vcdesc' n) :=
{ sdenote := sdenote_vcdesc' n
}.

Definition vcdesc := (sigT (fun (n : nat) => vcdesc' n)).

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

Section WITH_ENVD.

Variable ENVD : vcdesc.
Notation ENVD_SIZE := (projT1 ENVD).
Notation ENVD_DESC := (projT2 ENVD).

Inductive base_term : cdesc -> Set :=
| SLit   : str -> base_term (Desc str_d)
| NLit   : num -> base_term (Desc num_d)
| Var    : forall (i : fin ENVD_SIZE), base_term (svec_ith ENVD_DESC i)
| CompFd : forall ct, base_term (Comp ct) -> base_term (Desc fd_d)
.

(*I only want handler and all things it depends on to
 require a component type and message type. I don't want them
 to require a full message and component. This hopefully will
 eliminate the need to do some casts.*)
Inductive hdlr_term (ct : COMPT) (tag : fin NB_MSG) : cdesc -> Set :=
| Base  : forall {d}, base_term d -> hdlr_term ct tag d
| CComp   : hdlr_term ct tag (Comp ct)
| CConf : forall (i : fin (projT1 (comp_conf_desc ct))),
            hdlr_term ct tag (Desc (svec_ith (projT2 (comp_conf_desc ct)) i))
| MVar  : forall (i : fin (projT1 (lkup_tag tag))),
            hdlr_term ct tag (Desc (svec_ith (projT2 (lkup_tag tag)) i))
| StVar : forall (i : fin KSTD_SIZE), hdlr_term ct tag (svec_ith KSTD_DESC i)
.

Section WITH_TERM.

Variable TERM : cdesc -> Set.

Inductive expr : cdesc -> Set :=
| Term  : forall {d}, TERM d -> expr d
| UnOp  : forall {d1 d2}, unop d1 d2 -> expr d1 -> expr d2
| BinOp : forall {d1 d2 d3}, binop d1 d2 d3 -> expr d1 -> expr d2 -> expr d3
.

Fixpoint payload_cexpr' (n : nat) (pd : vcdesc' n) : Type :=
  match n as _n return vcdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vcdesc' (S n')) =>
    match pd with
    | (d, pd') => expr d * payload_cexpr' n' pd'
    end
  end%type pd.

Definition payload_cexpr pd := payload_cexpr' (projT1 pd) (projT2 pd).

Fixpoint payload_expr' (n : nat) (pd : vdesc' n) : Type :=
  match n as _n return vdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vdesc' (S n')) =>
    match pd with
    | (d, pd') => expr (Desc d) * payload_expr' n' pd'
    end
  end%type pd.

Definition payload_expr pd := payload_expr' (projT1 pd) (projT2 pd).

Section WITH_PROG_ENV.

Variable ENV : s[[ ENVD ]].
Variable KST : s[[ KSTD ]].

Fixpoint eval_base_term {d} (t : base_term d) : s[[ d ]] :=
  match t with
  | SLit s       => s
  | NLit n       => n
  | Var i        => shvec_ith _ (projT2 ENVD) ENV i
  | CompFd ct t' => comp_fd (projT1 (eval_base_term t'))
  end.

Definition eval_hdlr_term {d} (t : hdlr_term CT CTAG d)
  : s[[ d ]] :=
  match t with
  | Base _ bt => eval_base_term bt
  | CComp       => existT _ CC (Logic.eq_refl CT)
  | CConf i   => shvec_ith _ (projT2 CCONFD) (comp_conf CC) i
  | MVar i    => shvec_ith _ (projT2 CPAY) (pay CMSG) i
  | StVar i   => shvec_ith _ (projT2 KSTD) KST i
  end.

Variable EVAL_TERM : forall (d : cdesc), TERM d -> s[[ d ]].

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

Fixpoint eval_payload_cexpr' (n : nat) :
  forall (pd : vcdesc' n), payload_cexpr' n pd -> s[[ pd ]] :=
  let res n pd := payload_cexpr' n pd -> s[[ pd ]] in
  match n as _n return
    forall (pd : vcdesc' _n), res _n pd
  with
  | O => fun _ _ => tt
  | S n' => fun pd =>
    let (d, pd') as _pd return res (S n') _pd := pd in
    fun e =>
      let (v, e') := e in
      (eval_expr v, eval_payload_cexpr' n' pd' e')
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

Definition eval_payload_cexpr (pd : vcdesc) (e : payload_cexpr pd) : s[[ pd ]] :=
  eval_payload_cexpr' (projT1 pd) (projT2 pd) e.

Definition eval_payload_expr (pd : vdesc) (e : payload_expr pd) : s[[ pd ]] :=
  eval_payload_expr' (projT1 pd) (projT2 pd) e.

Definition sdenote_desc_cfg_pat (d : desc) : Set := option (expr (Desc d)).

Record comp_pat : Set :=
{ comp_pat_type : COMPT
; comp_pat_conf : shvec sdenote_desc_cfg_pat (projT2 (comp_conf_desc comp_pat_type))
}.

Definition sdenote_desc_conc_pat (d : desc) : Set := option (s[[ d ]]).

Record conc_pat : Set :=
{ conc_pat_type : COMPT
; conc_pat_conf : shvec sdenote_desc_conc_pat (projT2 (comp_conf_desc conc_pat_type))
}.

Definition elt_match (d : desc) (elt : s[[d]]) (elt' : sdenote_desc_cfg_pat d) : bool :=
  match elt' with
  | None   => true
  | Some x =>
    match d as _d return s[[_d]] -> s[[_d]] -> bool with
    | num_d => fun elt x => if num_eq x elt then true else false
    | str_d => fun elt x => if str_eq x elt then true else false
    | fd_d  => fun elt x => if fd_eq x elt then true else false
    end elt (eval_expr x)
  end.

Definition match_comp (cp : comp_pat) (c : comp) : bool :=
  match c, cp with
  | Build_comp t f cfg, Build_comp_pat t' cfgp =>
    match COMPTDEC t t' with
    | left EQ =>

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

Inductive cmd : Type :=
| Nop : cmd
| Seq : cmd -> cmd -> cmd
| Ite : expr (Desc num_d) -> cmd -> cmd -> cmd
| Send : forall ct, expr (Comp ct) -> forall (t : fin NB_MSG), payload_expr (lkup_tag t) -> cmd
| SendAll : comp_pat -> forall (t : fin NB_MSG), payload_expr (lkup_tag t) -> cmd
| Spawn :
    forall (t : COMPT), s[[ comp_conf_desc t ]] ->
    forall (i : fin ENVD_SIZE), svec_ith ENVD_DESC i = Comp t -> cmd
| Call : expr (Desc str_d) -> list (expr (Desc str_d)) ->
    forall (i : fin ENVD_SIZE), svec_ith ENVD_DESC i = Desc fd_d -> cmd
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

Definition shvec_replace_cast {d} {i : fin ENVD_SIZE} (EQ : svec_ith ENVD_DESC i = d) e v
  :=
  shvec_replace_ith sdenote_cdesc _ e i
    (match EQ in _ = _d return s[[ _d ]] -> _ with Logic.eq_refl => fun x => x end v).

Definition eval_base_expr {d} (e : s[[ENVD]]) : expr base_term d -> s[[ d ]] :=
  eval_expr base_term (@eval_base_term e).

Definition eval_base_payload_cexpr e :=
  eval_payload_cexpr base_term (@eval_base_term e).

Definition eval_base_payload_expr e :=
  eval_payload_expr base_term (@eval_base_term e).

Definition eval_hdlr_expr {d} (e : s[[ENVD]]) (s : s[[KSTD]])
  : expr (hdlr_term CT CTAG) d -> s[[ d ]] :=
  eval_expr (hdlr_term CT CTAG) (@eval_hdlr_term e s).

Definition eval_hdlr_payload_cexpr e s :=
  eval_payload_cexpr (hdlr_term CT CTAG) (@eval_hdlr_term s e).

Definition eval_hdlr_payload_expr e s :=
  eval_payload_expr (hdlr_term CT CTAG) (@eval_hdlr_term s e).

Definition ktrace_send_msgs (cps : list comp) (m : msg) : KTrace :=
  (map (fun c => KSend c m) cps).

Fixpoint init_state_run_cmd (s : init_state) (cmd : cmd base_term) : init_state :=
  let (cs, tr, e, st, fds) := s in
  match cmd with

  | Nop => s

  | Seq c1 c2 =>
    let s1 := init_state_run_cmd s c1 in
    let s2 := init_state_run_cmd s1 c2 in
    s2

  | Ite cond c1 c2 =>
    if num_eq (@eval_base_expr _ e cond) FALSE
    then init_state_run_cmd s c2
    else init_state_run_cmd s c1

  | Send ct ce t me =>
    let c := eval_base_expr e ce in
    let m := eval_base_payload_expr e _ me in
    let msg := (Build_msg t m) in
    {| init_comps := cs
     ; init_ktr   := tr ~~~ KSend (projT1 c) msg :: tr
     ; init_env   := e
     ; init_kst   := st
     ; init_fds   := fds
     |}

  | SendAll cp t me =>
    let m := eval_base_payload_expr e _ me in
    let msg := (Build_msg t m) in
    let comps := filter_comps base_term (@eval_base_term e) cp cs in
    {| init_comps := cs
     ; init_ktr   := tr ~~~ ktrace_send_msgs comps msg ++ tr
     ; init_env   := e
     ; init_kst   := st
     ; init_fds   := fds
     |}

  | Spawn ct cfg i EQ =>
    let c_fd := oracle fd_d (inhabit_unpack tr expand_ktrace) in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| init_comps := c :: cs
     ; init_ktr   := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
     ; init_env   := shvec_replace_cast EQ e (existT _ c (Logic.eq_refl _))
     ; init_kst   := st
     ; init_fds   := FdSet.add (comp_fd c) fds
     |}

  | Call ce argse i EQ =>
    let f := oracle fd_d (inhabit_unpack tr expand_ktrace) in
    let c := eval_base_expr e ce in
    let args := map (eval_base_expr e) argse in
    {| init_comps := cs
     ; init_ktr   := tr ~~~ KCall c args f :: tr
     ; init_env   := shvec_replace_cast EQ e f
     ; init_kst   := st
     ; init_fds   := FdSet.add f fds
     |}

  | StUpd i ve =>
    let v := eval_base_expr e ve in
    {| init_comps := cs
     ; init_ktr   := tr
     ; init_env   := e
     ; init_kst   := shvec_replace_ith _ _ st i v
     ; init_fds   := fds
     |}

  end.

Record hdlr_state :=
{ hdlr_kst : kstate
; hdlr_env : s[[ ENVD ]]
}.

(* This should probably move out once the environment can change *)
Fixpoint hdlr_state_run_cmd (s : hdlr_state) (cmd : cmd (hdlr_term CT CTAG))
  : hdlr_state :=
  let (s', env) := s in
  let (cs, tr, st, fd) := s' in
  match cmd with

  | Nop => s

  | Seq c1 c2 =>
    let s1 := hdlr_state_run_cmd s  c1 in
    let s2 := hdlr_state_run_cmd s1 c2 in
    s2

  | Ite cond c1 c2 =>
    if num_eq (@eval_hdlr_expr _ env st cond) FALSE
    then hdlr_state_run_cmd s c2
    else hdlr_state_run_cmd s c1

  | Send ct ce t me =>
    let c := eval_hdlr_expr env st ce in
    let m := eval_hdlr_payload_expr st env _ me in
    let msg := (Build_msg t m) in
    {| hdlr_kst :=
         {| kcs := cs
          ; ktr := tr ~~~ KSend (projT1 c) msg :: tr
          ; kst := st
          ; kfd := fd
          |}
     ; hdlr_env := env
    |}

  | SendAll cp t me =>
    let m := eval_hdlr_payload_expr st env _ me in
    let msg := (Build_msg t m) in
    let comps := filter_comps (hdlr_term CT CTAG) (@eval_hdlr_term env st) cp cs in
    {| hdlr_kst :=
         {| kcs := cs
          ; ktr := tr ~~~ ktrace_send_msgs comps msg ++ tr
          ; kst := st
          ; kfd := fd
          |}
     ; hdlr_env := env
    |}

  | Spawn ct cfg i EQ =>
    let c_fd := oracle fd_d (inhabit_unpack tr expand_ktrace) in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| hdlr_kst :=
         {| kcs := c :: cs
          ; ktr := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
          ; kst := st
          ; kfd := FdSet.add (comp_fd c) fd
          |}
     ; hdlr_env := shvec_replace_cast EQ env (existT _ c (Logic.eq_refl _))
     |}

  | Call ce argse i EQ =>
    let f := oracle fd_d (inhabit_unpack tr expand_ktrace) in
    let c := eval_hdlr_expr env st ce in
    let args := map (eval_hdlr_expr env st) argse in
    {| hdlr_kst :=
         {| kcs := cs
          ; ktr := tr ~~~ KCall c args f :: tr
          ; kst := st
          ; kfd := FdSet.add f fd
          |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}

  | StUpd i ve =>
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

Definition default_hdlr_state s :=
  {| hdlr_kst := s; hdlr_env := default_cpayload ENVD |}.

Definition kstate_run_prog (s : kstate) (p : hdlr_prog CT CTAG) : kstate :=
  hdlr_kst (hdlr_state_run_cmd (default_hdlr_state s) p).

End WITH_ENVD.

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
  sigT (fun prog_envd => hdlr_prog prog_envd ct tag).

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
  match n with
  | 0 => fun _ _ => FdSet.empty
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vcdesc' (S n') _v -> FdSet.t) := v in
    match d with
    | Desc fd_d => fun vv =>
      let (vd, vv') := vv in
      FdSet.add vd (vcdesc_fds_set' n' v' vv')
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

Inductive InitialState : kstate -> Prop :=
| C_is : forall s,
           s = init_state_run_cmd IENVD initial_init_state IPROG ->
           InitialState {| kcs := init_comps _ s
                           ; ktr := init_ktr _ s
                           ; kst := init_kst _ s
                           ; kfd := FdSet.union
                                      (vcdesc_fds_set _ (init_kst _ s))
                                      (vcdesc_fds_set _ (init_env _ s))
                        |}.

Inductive ValidExchange (c:comp) (m:msg) : kstate -> kstate -> Prop :=
| C_ve : forall s tr s',
           let cs := kcs s in
           ktr s = [tr]%inhabited ->
           s' = {| kcs := cs
                   ; ktr := [KRecv c m :: KSelect cs c :: tr]
                   ; kst := kst s
                   ; kfd := FdSet.union (vdesc_fds_set _ (pay m)) (kfd s)
                |} ->
           let hdlrs := HANDLERS (tag m) (comp_type c) in
           ValidExchange c m s (kstate_run_prog c m (projT1 hdlrs) s'
                                                (projT2 hdlrs)).

Inductive Reach : kstate -> Prop :=
| Reach_init :
  forall s,
  InitialState s ->
  Reach s
| Reach_valid :
  forall c m s s',
  Reach s ->
  ValidExchange c m s s' ->
  Reach s'
| Reach_bogus :
  forall s s' f bmsg tr,
  let cs := kcs s in
  ktr s = [tr]%inhabited ->
  Reach s ->
  (* introducing s' makes it easier to eapply Reach_bogus *)
  s' = {| kcs := cs
        ; ktr := [KBogus f bmsg :: KSelect cs f :: tr]
        ; kst := kst s
        ; kfd := kfd s
        |} ->
  Reach s'
.

Definition all_open_set s := all_open (FdSet.elements s).

Definition all_open_set_drop f s := all_open (FdSet.elements (FdSet.remove f s)).

Fixpoint all_open_set_drop_all fs s :=
  match fs with
  | nil    => all_open_set s
  | f::fs' => all_open_set_drop_all fs' (FdSet.remove f s)
  end.

Definition all_fds_in l s := List.Forall (fun x => FdSet.In (comp_fd x) s) l.

Definition vdesc_fds_subset {envd : vdesc} (env : s[[envd]]) (s : FdSet.t) :=
  FdSet.Subset (vdesc_fds_set envd env) s.

Definition vcdesc_fds_subset {envd : vcdesc} (env : s[[envd]]) (s : FdSet.t) :=
  FdSet.Subset (vcdesc_fds_set envd env) s.

Definition init_invariant {envd} (s : init_state envd) :=
  let fds := init_fds _ s in
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
  (s : FdSet.t) (ht : hdlr_term ENVD (comp_type CC) (tag CMSG) d) (f : s[[ d ]])
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

Definition open_payload_frame_expr {term : cdesc -> Set} {d}
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

Definition open_payload_frame_base_expr {ENVD : vcdesc} {d}
  (e : s[[ENVD]]) cs (fds : FdSet.t) (exp : expr (base_term ENVD) d) (res : s[[d]]) : hprop
  :=
  open_payload_frame_base_expr' fds exp res
  * [all_fds_in cs fds]
  * [vcdesc_fds_subset e fds]
.

Definition open_payload_frame_hdlr_expr' {CC CMSG ENVD d} (s : FdSet.t)
  : expr (hdlr_term ENVD (comp_type CC) (tag CMSG)) d -> s[[d]] -> hprop
  := open_payload_frame_expr (open_payload_frame_hdlr s).

Definition open_payload_frame_hdlr_expr {CC CMSG} {ENVD : vcdesc} {d}
  (e : s[[ENVD]]) cs cm (fds : FdSet.t)
  (exp : expr (hdlr_term ENVD (comp_type CC) (tag CMSG)) d)
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

Definition trace_send_msg_comps (cps : list comp) (m : msg) : Trace :=
  flat_map (fun c => trace_send_msg (comp_fd c) m) cps.

Theorem all_open_set_unpack : forall x s, FdSet.In x s ->
  all_open_set s ==>
  open x * all_open_set_drop x s.
Proof.
  intros. unfold all_open_set, all_open_set_drop.
  apply himp_trans with (Q := open x * all_open_drop (FdSet.elements s) x).
  apply unpack_all_open.
  apply FdSet.elements_spec1 in H.
  apply SetoidList.InA_alt in H.
  destruct H as [y [EQ IN] ]. now inversion_clear EQ.
  sep'.
  (* TODO: this is tedious *)
Admitted.

Theorem all_open_set_pack : forall x s, FdSet.In x s ->
  open x * all_open_set_drop x s ==>
  all_open_set s.
Proof.
  (* TODO: Just copy on all_open_set_unpack *)
  intros.
Admitted.

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
  apply all_open_set_unpack. now inversion H0.
  rewrite app_assoc; sep''.
  apply all_open_set_pack. now inversion H.
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

Definition run_init_cmd :
  forall (envd : vcdesc) (s : init_state envd)
         (c : cmd envd (base_term envd)),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' * traced (expand_ktrace tr) *
          [s' = init_state_run_cmd envd s c]).
Proof.
  intros envd sinit cinit;
  refine (Fix2
    (fun c s => tr :~~ init_ktr envd s in
      init_invariant s * traced (expand_ktrace tr))
    (fun c s (s' : init_state envd) => tr :~~ init_ktr envd s' in
      init_invariant s' * traced (expand_ktrace tr)
      * [s' = init_state_run_cmd envd s c])
    (fun self c s => _) cinit sinit
  ).
  destruct s as [cs tr e st fds]_eqn.

  refine (
    match c with

    | Nop => {{ Return s }}

    | Seq c1 c2 =>
      s1 <- self c1 s;
      s2 <- self c2 s1
        <@> [s1 = init_state_run_cmd envd s c1];
      {{ Return s2 }}

    | Ite cond c1 c2 =>
      if num_eq (eval_base_expr envd e cond) FALSE
      then s' <- self c2 s; {{ Return s' }}
      else s' <- self c1 s; {{ Return s' }}

    | Send ct ce t me =>
      let c := projT1 (eval_base_expr envd e ce) in
      let m := eval_base_payload_expr _ e _ me in
      let msg := Build_msg t m in
      send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
        <@> all_open_set_drop (comp_fd c) fds * [In c cs] * [vcdesc_fds_subset e fds];;

      let tr := tr ~~~ KSend c msg :: tr in
      {{ Return {| init_comps := cs
                 ; init_ktr   := tr
                 ; init_env   := e
                 ; init_kst   := st
                 ; init_fds   := fds
                |}
      }}

    | SendAll cp t me =>
      let m := eval_base_payload_expr _ e _ me in
      let comps := filter_comps (base_term _) (@eval_base_term _ e) cp cs in
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

    | Spawn ct cfg i EQ =>
      let c_cmd := compd_cmd (COMPS ct) in
      let c_args := compd_args (COMPS ct) in
      c_fd <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
           <@> init_invariant s;

      let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
      let tr := tr ~~~ KExec c_cmd c_args c :: tr in
      {{ Return {| init_comps := c :: cs
                 ; init_ktr   := tr
                 ; init_env   := shvec_replace_cast _ EQ e (existT _ c (Logic.eq_refl ct))
                 ; init_kst   := st
                 ; init_fds   := FdSet.add c_fd fds
                |}
      }}

    | Call ce argse i EQ =>
      let c := eval_base_expr envd e ce in
      let args := map (eval_base_expr envd e) argse in
      f <- call c args (tr ~~~ expand_ktrace tr)
           <@> init_invariant s;

      let tr := tr ~~~ KCall c args f :: tr in
      {{ Return {| init_comps := cs
                 ; init_ktr   := tr
                 ; init_env   := shvec_replace_cast _ EQ e f
                 ; init_kst   := st
                 ; init_fds   := FdSet.add f fds
                |}
      }}

    | StUpd i ve =>
      let v := eval_base_expr _ e ve in
      {{ Return {| init_comps := cs
                 ; init_ktr   := tr
                 ; init_env   := e
                 ; init_kst   := shvec_replace_ith _ _ st i v
                 ; init_fds   := fds
                |}
      }}

    end
  ); sep''.

(* Ite *)
  destruct (num_eq (eval_base_expr envd e cond) FALSE).
  reflexivity. contradiction.
  destruct (num_eq (eval_base_expr envd e cond) FALSE).
  contradiction. reflexivity.

(* Send *)
  unfold c0. clear c0.

  dependent inversion ce with (
    fun _d _ce =>
    match _d as __d return expr _ __d -> _ with
    | Comp _ => fun ce =>
      all_open_set fds ==>
      all_open_set_drop (comp_fd (projT1 (eval_base_expr envd e ce))) fds *
      open (comp_fd (projT1 (eval_base_expr envd e ce)))
    | _      => fun _ => False
    end _ce
  ).
  simpl. subst.

  assert (FdSet.In (comp_fd (projT1 (eval_base_term envd e b))) fds).

(* This one is actually hard to get through! *)

(*
  refine (
    match b as _b in base_term _ _d return
      forall (EQ : _d = Comp ct),
      match _d with
      | Comp _ =>
        FdSet.In (comp_fd (projT1 (
          match EQ in _ = _e return s[[ _e ]] with
          | Logic.eq_refl => eval_base_term envd e _b
          end
        ))) fds
      | _      => False
      end
    with
    | Var i => fun EQ => _
    | _     => fun EQ => _
    end (Logic.eq_refl (Comp ct))
  ); try discriminate.
*)

  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
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
  admit.
  admit.
  admit.
Qed.

Definition run_hdlr_cmd :
  forall (cc : comp) (cm : msg) (envd : vcdesc) (s : hdlr_state envd)
         (c : cmd envd (hdlr_term envd (comp_type cc) (tag cm))),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cc cm s * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cc cm s' * traced (expand_ktrace tr)
          * [s' = hdlr_state_run_cmd cc cm envd s c]).
Proof.
  intros cc cm envd sinit cinit;
  refine (Fix2
    (fun c s => tr :~~ ktr (hdlr_kst _ s) in
      hdlr_invariant cc cm s * traced (expand_ktrace tr))
    (fun c s (s' : hdlr_state envd) => tr :~~ ktr (hdlr_kst _ s') in
      hdlr_invariant cc cm s' * traced (expand_ktrace tr)
      * [s' = hdlr_state_run_cmd cc cm envd s c]
    )
    (fun self c s => _) cinit sinit
  ).
  destruct s as [ [cs tr st fds] env ]_eqn.

  refine (
  (* /!\ We lose track of the let-open equalities if existentials remain,
         make sure that Coq can infer _all_ the underscores. *)
  match c with

  | Nop => {{ Return s }}

  | Seq c1 c2 =>
    s1 <- self c1 s;
    s2 <- self c2 s1
       <@> [s1 = hdlr_state_run_cmd _ _ envd s c1];
    {{ Return s2 }}

  | Ite cond c1 c2 =>
    if num_eq (eval_hdlr_expr _ _ envd env st cond) FALSE
    then s' <- self c2 s; {{ Return s' }}
    else s' <- self c1 s; {{ Return s' }}

  | Send ct ce t me =>
    let (c, _) := eval_hdlr_expr _ _ _ _ _ ce in
    let m := eval_hdlr_payload_expr cc cm envd st env _ me in
    let msg := Build_msg t m in
    send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
    <@> [In c cs]
      * [all_fds_in cs fds]
      * [vcdesc_fds_subset env fds]
      * [vdesc_fds_subset (pay cm) fds];;

    let tr := tr ~~~ KSend c msg :: tr in
    {{ Return {| hdlr_kst := {| kcs := cs ; ktr := tr ; kst := st ; kfd := fds |}
               ; hdlr_env := env
               |}
    }}

  | SendAll cp t me =>
    let m := eval_hdlr_payload_expr cc cm envd st env _ me in
    let comps := filter_comps (hdlr_term envd _ (tag cm))
                              (@eval_hdlr_term _ cm envd env st) cp cs in
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

  | Spawn ct cfg i EQ =>
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
               ; hdlr_env := shvec_replace_cast _ EQ env (existT _ c (Logic.eq_refl ct))
               |}
    }}

  | Call ce argse i EQ =>
    let c := eval_hdlr_expr _ _ _ _ _ ce in
    let args := map (eval_hdlr_expr _ _ _ _ _) argse in
    f <- call c args (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s;

    let tr := tr ~~~ KCall c args f :: tr in
    {{ Return {| hdlr_kst := {| kcs := cs
                              ; ktr := tr
                              ; kst := st
                              ; kfd := FdSet.add f fds |}
               ; hdlr_env := shvec_replace_cast _ EQ env f
               |}
    }}

  | StUpd i ve =>
    let v := eval_hdlr_expr cc cm envd env st ve in
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

(* Ite *)
  destruct (num_eq (eval_hdlr_expr cc cm envd env st cond) FALSE).
  reflexivity. contradiction.
  destruct (num_eq (eval_hdlr_expr cc cm envd env st cond) FALSE).
 contradiction. reflexivity.

admit.
admit.
admit.
admit.
admit.
admit.
rewrite Heqh. simpl. admit.
repeat f_equal. sep''. unfold c0. now f_equal. (* ok so the oracle thing works *)
admit.
admit.
admit.
admit.
admit.
admit.
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

  isolate (
    traced (Select (proj_fds cs) (comp_fd c) :: expand_ktrace x0) ==>
    traced (expand_ktrace x)
  ).
  admit.
  admit. (* easy *)

  admit. (* combine 'In c (proj_fds cs)' and 'all_fds_in cs fds' *)

  (*unfold s'. simpl.*)
  isolate (
    traced (trace_recv_msg (comp_fd c) m ++ expand_ktrace x0) ==>
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
