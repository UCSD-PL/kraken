Require Import Ascii.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Coq.Logic.Eqdep.
Require Import NPeano.
Require Orders.
Require Import List.
Require Import ListSet.
Require Morphisms.
Require Import RelationClasses.
Require Import String.
Require Import Sumbool.
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

Definition vdesc' : nat -> Set := svec desc.

Definition sdenote_vdesc' n (pt : vdesc' n) : Set :=
  shvec sdenote_desc pt.

Instance SDenoted_vdesc' {n} : SDenoted (vdesc' n) :=
{ sdenote := sdenote_vdesc' n
}.

(* Thank you Ynot for breaking sigT notation... *)
Definition vdesc := sigT vdesc'.

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

Fixpoint vdesc_fds' (n : nat) :
  forall (v : vdesc' n), sdenote_vdesc' n v -> list fd :=
  match n with
  | 0 => fun _ _ => nil
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vdesc' (S n') _v -> list fd) := v in
    match d with
    | fd_d => fun vv =>
      let (vd, vv') := vv in
      vd :: (vdesc_fds' n' v' vv')
    | _ => fun vv =>
      let (_, vv') := vv in
      vdesc_fds' n' v' vv'
    end
  end.

Definition vdesc_fds v := vdesc_fds' (projT1 v) (projT2 v).

Fixpoint vcdesc_fds' (n : nat) :
  forall (v : vcdesc' n), sdenote_vcdesc' n v -> list fd :=
  match n as n return forall (v : vcdesc' n), sdenote_vcdesc' n v -> list fd with
  | 0 => fun _ _ => nil
  | S n' => fun v =>
    let (d, v') as _v return (sdenote_vcdesc' (S n') _v -> list fd) := v in
    match d with
    | Desc fd_d => fun vv =>
      let (vd, vv') := vv in
      vd :: (vcdesc_fds' n' v' vv')
    | Comp c => fun vv =>
      let (vd, vv') := vv in
      (comp_fd (projT1 vd)) :: (vcdesc_fds' n' v' vv')
    | _ => fun vv =>
      let (_, vv') := vv in
      vcdesc_fds' n' v' vv'
    end
  end.

Definition vcdesc_fds v := vcdesc_fds' (projT1 v) (projT2 v).

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

Definition in_if_fd_desc {n} {vd:svec desc n} (v:s[[vd]]) i fds : Prop :=
  match svec_ith vd i as __d return s[[__d]] -> Prop with
  | fd_d => fun ith => In ith fds
  | _    => fun _ => True
  end (shvec_ith sdenote_desc vd v i).

Definition vdesc_fds_all_in {vd:vdesc} (v:s[[vd]]) fds :=
  forall i, in_if_fd_desc v i fds.

Definition comp_fds_in c fds :=
  In (comp_fd c) fds /\ vdesc_fds_all_in (comp_conf c) fds.

Definition in_if_fd_cdesc {n} {vd:svec cdesc n} (v:s[[vd]]) i fds : Prop :=
  match svec_ith vd i as __d return s[[__d]] -> Prop with
  | Desc d => match d as __d return s[[__d]] -> Prop with
              | fd_d => fun ith => In ith fds
              | _    => fun _ => True
              end
  | Comp c => fun ith => comp_fds_in (projT1 ith) fds
  end (shvec_ith sdenote_cdesc vd v i).

Definition vcdesc_fds_all_in {vd:vcdesc} (v:s[[vd]]) fds :=
  forall i, in_if_fd_cdesc v i fds.

Definition all_comp_fds_in cs fds :=
  forall c, In c cs -> comp_fds_in c fds.

Definition recv_payload' :
  forall (f : fd) (n : nat) (pd : vdesc' n) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun pv : s[[ pd ]] => tr ~~
          traced (trace_payload_recv' f n pd pv ++ tr) * open f
          * all_open (vdesc_fds' n pd pv)
        ).
Proof.
  intros; refine (
    Fix3
      (fun n pd tr => tr ~~ traced tr * open f)
      (fun n pd tr (pv : s[[ pd ]]) => tr ~~
        traced (trace_payload_recv' f n pd pv ++ tr) * open f
        * all_open (vdesc_fds' n pd pv))
      (fun self (n : nat) (pd : vdesc' n) tr =>
         match n as _n return
           forall (pd : vdesc' _n), STsep _ (fun x : s[[ pd ]] => _)
         with
         | O => fun _ => {{ Return tt }}
         | S n' => fun pt =>
           match pt with
           | (d, pt') =>
             v  <- recv_arg f d tr;
             vs <- self n' pt' (tr ~~~ trace_recv f d v ++ tr)
               <@> open_if_fd _ v;
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
          * all_open (vdesc_fds _ pv)
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
          * match m with
            | inl msg => all_open (vdesc_fds _ (pay msg))
            | inr bog => emp
            end
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
| KExec      : str -> list str -> comp -> KAction
| KCall      : str -> list str -> fd -> KAction
| KInvokeFD  : str -> list str -> fd -> KAction
| KInvokeStr : str -> list str -> str -> KAction
| KSelect    : list comp -> comp -> KAction
| KSend      : comp -> msg -> KAction
| KRecv      : comp -> msg -> KAction
| KBogus     : comp -> bogus_msg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args c => Exec cmd args (comp_fd c) :: nil
  | KCall cmd args pipe => Call cmd args pipe :: nil
  | KInvokeFD cmd args pipe => InvokeFD cmd args pipe :: nil
  | KInvokeStr cmd args res => InvokeStr cmd args res :: nil
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
  }.

Inductive unop : cdesc -> cdesc -> Set :=
| Not : unop (Desc num_d) (Desc num_d)
| SplitFst : ascii -> unop (Desc str_d) (Desc str_d)
| SplitSnd : ascii -> unop (Desc str_d) (Desc str_d)
| UnopNum : forall (d:cdesc), (s[[d]] -> num) ->
              unop d (Desc num_d)
| UnopStr : forall (d:cdesc), (s[[d]] -> str) ->
              unop d (Desc str_d)
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
  | UnopNum _ op => fun v => op v
  | UnopStr _ op => fun v => op v
  end v.

Implicit Arguments eval_unop.

Inductive binop : cdesc -> cdesc -> cdesc -> Set :=
| Eq    : forall d, binop d d (Desc num_d)
| Lt    : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Add   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Sub   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Mul   : binop (Desc num_d) (Desc num_d) (Desc num_d)
| Cat   : binop (Desc str_d) (Desc str_d) (Desc str_d)
| BinopNum : forall (d1 d2:cdesc), (s[[d1]] -> s[[d2]] -> num) ->
               binop d1 d2 (Desc num_d)
| BinopStr : forall (d1 d2:cdesc), (s[[d1]] -> s[[d2]] -> str) ->
               binop d1 d2 (Desc str_d)
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
  | Lt  => fun n1 n2 : num =>
    if Compare_dec.lt_dec (nat_of_num n1) (nat_of_num n2)
    then TRUE else FALSE
  | Add => fun v1 v2 : num =>
    num_of_nat (plus (nat_of_num v1) (nat_of_num v2))
  | Sub => fun v1 v2 : num =>
    num_of_nat (minus (nat_of_num v1) (nat_of_num v2))
  | Mul => fun v1 v2 : num =>
    num_of_nat (mult (nat_of_num v1) (nat_of_num v2))
  | Cat => fun v1 v2 : str =>
    v1 ++ v2
  | BinopNum _ _ op => fun v1 v2 => op v1 v2
  | BinopStr _ _ op => fun v1 v2 => op v1 v2
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
| CConf : forall ct' (i : fin (projT1 (comp_conf_desc ct'))),
            hdlr_term ct tag envd (Comp ct') ->
            hdlr_term ct tag envd (Desc (svec_ith (projT2 (comp_conf_desc ct')) i))
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

Fixpoint payload_oexpr' envd (n : nat) (pd : vdesc' n) : Type :=
  match n as _n return vdesc' _n -> Type with
  | O => fun p => unit
  | S n' => fun (pd : vdesc' (S n')) =>
    match pd with
    | (d, pd') => option (expr envd (Desc d)) * payload_oexpr' envd n' pd'
    end
  end%type pd.

Definition payload_oexpr envd pd := payload_oexpr' envd (projT1 pd) (projT2 pd).

Definition sdenote_desc_cfg_pat envd (d : desc) : Set := option (expr envd (Desc d)).

Record comp_pat envd : Type :=
{ comp_pat_type : COMPT
; comp_pat_conf : payload_oexpr envd (comp_conf_desc comp_pat_type)
}.

Definition sdenote_desc_conc_pat (d : desc) : Set := option (s[[ d ]]).

Record conc_pat : Set :=
{ conc_pat_type : COMPT
; conc_pat_conf : shvec sdenote_desc_conc_pat (projT2 (comp_conf_desc conc_pat_type))
}.

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

Fixpoint eval_hdlr_term {d envd} (t : hdlr_term CT CTAG envd d) env
  : s[[ d ]] :=
  match t with
  | Base _ bt => eval_base_term env bt
  | CComp       => existT _ CC (Logic.eq_refl CT)
  | CConf ct i c   => let cp := eval_hdlr_term c env in
    match (projT2 cp) in _ = _ct return
      forall (_i:fin (projT1 (comp_conf_desc _ct))),
        s[[svec_ith (projT2 (comp_conf_desc _ct)) _i]]
    with
    | Logic.eq_refl => fun i =>
      shvec_ith _ _ (comp_conf (projT1 cp)) i
    end i
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

Definition eval_oexpr {d envd} env (e : option (expr envd d)) : option s[[ d ]] :=
  match e with
  | Some e => Some (eval_expr env e)
  | None   => None
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

Fixpoint eval_payload_oexpr' envd env (n : nat) :
  forall (pd : vdesc' n), payload_oexpr' envd n pd -> shvec sdenote_desc_conc_pat pd :=
  let res n pd := payload_oexpr' envd n pd -> shvec sdenote_desc_conc_pat pd in
  match n as _n return
    forall (pd : vdesc' _n), res _n pd
  with
  | O => fun _ _ => tt
  | S n' => fun pd =>
    let (d, pd') as _pd return res (S n') _pd := pd in
    fun e =>
      let (v, e') := e in
      (eval_oexpr env v, eval_payload_oexpr' envd env n' pd' e')
  end.

Definition eval_payload_cexpr envd env (pd : vcdesc) (e : payload_cexpr envd pd) : s[[ pd ]] :=
  eval_payload_cexpr' envd env (projT1 pd) (projT2 pd) e.

Definition eval_payload_expr envd env (pd : vdesc) (e : payload_expr envd pd) : s[[ pd ]] :=
  eval_payload_expr' envd env (projT1 pd) (projT2 pd) e.

Definition eval_payload_oexpr envd env (pd : vdesc) (e : payload_oexpr envd pd)
  : shvec sdenote_desc_conc_pat (projT2 pd) :=
  eval_payload_oexpr' envd env (projT1 pd) (projT2 pd) e.

Definition elt_match (d : desc) (elt : s[[d]]) (elt' : sdenote_desc_conc_pat d) : bool :=
  match elt' with
  | None   => true
  | Some x =>
    match d as _d return s[[_d]] -> s[[_d]] -> bool with
    | num_d => fun elt x => if num_eq x elt then true else false
    | str_d => fun elt x => if str_eq x elt then true else false
    | fd_d  => fun elt x => if fd_eq x elt then true else false
    end elt x
  end.

Definition match_comp_pf (cp : conc_pat) (c : comp)
  : option (comp_type c = conc_pat_type cp) :=
  match COMPTDEC (comp_type c) (conc_pat_type cp) with
  | left EQ =>
    match EQ in _ = _t return
      shvec sdenote_desc_conc_pat (projT2 (comp_conf_desc _t)) -> _
    with
    | Logic.eq_refl => fun cfgp =>
      if shvec_match (projT2 (comp_conf_desc (comp_type c)))
                     sdenote_desc sdenote_desc_conc_pat
                     elt_match (comp_conf c) cfgp
      then Some EQ
      else None
    end (conc_pat_conf cp)
  | right _ => None
  end.

Definition match_comp (cp : conc_pat) (c : comp) : bool :=
  if match_comp_pf cp c
  then true
  else false.

Fixpoint find_comp (cp : conc_pat) (comps : list comp)
  : option (sigT (fun c : comp => comp_type c = conc_pat_type cp)) :=
  match comps with
  | nil => None
  | c::comps' => match match_comp_pf cp c with
                 | Some EQ => Some (existT _ c EQ)
                 | None    => find_comp cp comps'
                 end
  end.

Definition filter_comps (cp : conc_pat) (comps : list comp) :=
  filter (match_comp cp) comps.

Definition exists_comp (cp : conc_pat) (comps : list comp) :=
  match find_comp cp comps with
  | None   => false
  | Some _ => true
  end.

Inductive cmd : vcdesc -> Type :=
| Nop : forall envd, cmd envd
| Seq : forall envd, cmd envd -> cmd envd -> cmd envd
| Ite : forall envd, expr envd (Desc num_d) -> cmd envd -> cmd envd -> cmd envd
| Send : forall envd ct, expr envd (Comp ct) ->
  forall (t : fin NB_MSG), payload_expr envd (lkup_tag t) -> cmd envd
| Spawn :
    forall (envd : vcdesc) (t : COMPT), payload_expr envd (comp_conf_desc t) ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Comp t -> cmd envd
| Call : forall (envd : vcdesc), expr envd (Desc str_d) -> list (expr envd (Desc str_d)) ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Desc fd_d -> cmd envd
| InvokeFD : forall (envd : vcdesc), expr envd (Desc str_d) -> list (expr envd (Desc str_d)) ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Desc fd_d -> cmd envd
| InvokeStr : forall (envd : vcdesc), expr envd (Desc str_d) -> list (expr envd (Desc str_d)) ->
    forall (i : fin (projT1 envd)), svec_ith (projT2 envd) i = Desc str_d -> cmd envd
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
}.

End WITH_PROG_KST.

End WITH_TERM.

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
Hint Unfold eval_base_expr.

Definition eval_base_payload_cexpr :=
  eval_payload_cexpr base_term (fun d envd e => @eval_base_term d envd e).
Hint Unfold eval_base_payload_cexpr.

Definition eval_base_payload_expr :=
  eval_payload_expr base_term (fun d envd e => @eval_base_term d envd e).
Hint Unfold eval_base_payload_expr.

Definition eval_base_payload_oexpr :=
  eval_payload_oexpr base_term (fun d envd e => @eval_base_term d envd e).
Hint Unfold eval_base_payload_oexpr.

Definition eval_base_comp_pat envd env cp :=
  {| conc_pat_type := comp_pat_type _ _ cp;
     conc_pat_conf := eval_base_payload_oexpr envd env _ (comp_pat_conf _ _ cp) |}.

Definition eval_hdlr_expr {d} {envd : vcdesc} (s : s[[KSTD]])
  : s[[envd]] -> expr (hdlr_term CT CTAG) envd d -> s[[ d ]] :=
  eval_expr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).
Hint Unfold eval_hdlr_expr.

Definition eval_hdlr_payload_cexpr s :=
  eval_payload_cexpr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).
Hint Unfold eval_hdlr_payload_cexpr.

Definition eval_hdlr_payload_expr s :=
  eval_payload_expr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).
Hint Unfold eval_hdlr_payload_expr.

Definition eval_hdlr_payload_oexpr s :=
  eval_payload_oexpr (hdlr_term CT CTAG) (fun d envd e t => @eval_hdlr_term s d envd t e).
Hint Unfold eval_hdlr_payload_oexpr.

Definition eval_hdlr_comp_pat s envd env cp :=
  {| conc_pat_type := comp_pat_type _ _ cp;
     conc_pat_conf := eval_hdlr_payload_oexpr s envd env _ (comp_pat_conf _ _ cp) |}.

Definition ktrace_send_msgs (cps : list comp) (m : msg) : KTrace :=
  (map (fun c => KSend c m) cps).

Inductive InputTreeType :=
| FD : InputTreeType
| Str : InputTreeType
| Unit : InputTreeType
| Comb : InputTreeType -> InputTreeType -> InputTreeType.

Fixpoint run_cmd_it {envd : vcdesc} {term} (cmd : cmd term envd) : InputTreeType :=
  match cmd with
  | Spawn _ _ _ _ _ => FD
  | Call _ _ _ _ _ => FD
  | InvokeFD _ _ _ _ _ => FD
  | InvokeStr _ _ _ _ _ => Str
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
  | Str => str
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
    init_state_run_cmd envd (init_state_run_cmd envd s c1 (fst i)) c2 (snd i)

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
     |}

  | Spawn _ ct cfge i EQ => fun s i =>
    let tr := init_ktr _ s in
    let c_fd := i in
    let cfg := eval_base_payload_expr _ (init_env _ s) _ cfge in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| init_comps := c :: (init_comps _ s)
     ; init_ktr   := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
     ; init_env   := shvec_replace_cast EQ (init_env _ s) (existT _ c (Logic.eq_refl _))
     ; init_kst   := init_kst _ s
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
     |}

  | InvokeFD _ ce argse i EQ => fun s i =>
    let tr := init_ktr _ s in
    let f := i in
    let c := eval_base_expr (init_env _ s) ce in
    let args := map (eval_base_expr (init_env _ s)) argse in
    {| init_comps := init_comps _ s
     ; init_ktr   := tr ~~~ KInvokeFD c args f :: tr
     ; init_env   := shvec_replace_cast EQ (init_env _ s) f
     ; init_kst   := init_kst _ s
     |}

  | InvokeStr _ ce argse i EQ => fun s i =>
    let tr := init_ktr _ s in
    let res := i in
    let c := eval_base_expr (init_env _ s) ce in
    let args := map (eval_base_expr (init_env _ s)) argse in
    {| init_comps := init_comps _ s
     ; init_ktr   := tr ~~~ KInvokeStr c args res :: tr
     ; init_env   := shvec_replace_cast EQ (init_env _ s) res
     ; init_kst   := init_kst _ s
     |}

  | StUpd _ i ve => fun s _ =>
    let v := eval_base_expr (init_env _ s) ve in
    {| init_comps := init_comps _ s
     ; init_ktr   := init_ktr _ s
     ; init_env   := init_env _ s
     ; init_kst   := shvec_replace_ith _ _ (init_kst _ s) i v
     |}

  | CompLkup envd cp c1 c2 => fun s i =>
    let ocdp := find_comp (eval_base_comp_pat _ (init_env _ s) cp) (init_comps _ s) in
    match ocdp with
    | Some cdp =>
      let c := projT1 cdp in
      let d := Comp (comp_pat_type _ _ cp) in
      let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
      let s' := Build_init_state new_envd (init_comps _ s) (init_ktr _ s)
                                 (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                                              (existT _ c (projT2 cdp)) (projT2 envd) (init_env _ s))
                                 (init_kst _ s) in
      let s'' := init_state_run_cmd new_envd s' c1 (fst i) in
      {| init_comps := init_comps _ s''
       ; init_ktr   := init_ktr _ s''
       ; init_env   := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (init_env _ s'')
       ; init_kst   := init_kst _ s''
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
          |}
     ; hdlr_env := env
    |}

  | Spawn _ ct cfge i EQ => fun s i =>
    let (s', env) := s in
    let tr := ktr s' in
    let c_fd := i in
    let cfg := eval_hdlr_payload_expr (kst s') _ env _ cfge in
    let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
    let comp := COMPS ct in
    {| hdlr_kst :=
         {| kcs := c :: kcs s'
          ; ktr := tr ~~~ KExec (compd_cmd comp) (compd_args comp) c :: tr
          ; kst := kst s'
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
          |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}

  | InvokeFD _ ce argse i EQ => fun s i =>
    let (s', env) := s in
    let tr := ktr s' in
    let f := i in
    let c := eval_hdlr_expr (kst s') env ce in
    let args := map (eval_hdlr_expr (kst s') env) argse in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := tr ~~~ KInvokeFD c args f :: tr
          ; kst := kst s'
          |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}

  | InvokeStr _ ce argse i EQ => fun s i =>
    let (s', env) := s in
    let tr := ktr s' in
    let res := i in
    let c := eval_hdlr_expr (kst s') env ce in
    let args := map (eval_hdlr_expr (kst s') env) argse in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := tr ~~~ KInvokeStr c args res :: tr
          ; kst := kst s'
          |}
     ; hdlr_env := shvec_replace_cast EQ env res
     |}

  | StUpd _ i ve => fun s _ =>
    let (s', env) := s in
    let v := eval_hdlr_expr (kst s') env ve in
    {| hdlr_kst :=
         {| kcs := kcs s'
          ; ktr := ktr s'
          ; kst := shvec_replace_ith _ _ (kst s') i v
          |}
     ; hdlr_env := env
     |}

  | CompLkup envd cp c1 c2 => fun s i =>
    let (s', env) := s in
    let ocdp := find_comp (eval_hdlr_comp_pat (kst s') _ env cp) (kcs s') in
    match ocdp with
    | Some cdp =>
      let c := projT1 cdp in
      let d := Comp (comp_pat_type _ _ cp) in
      let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
      let s' := Build_hdlr_state new_envd {| kcs := kcs s'
                                           ; ktr := ktr s'
                                           ; kst := kst s'
                                           |}
                                (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                                              (existT _ c (projT2 cdp)) (projT2 envd) env) in
      let s'' := hdlr_state_run_cmd new_envd s' c1 (fst i) in
(*      let ks'' := hdlr_kst _ s'' in
      let new_env := hdlr_env _ s'' in*)
      {| hdlr_kst := hdlr_kst _ s''
(*           {| kcs := kcs ks''
            ; ktr := ktr ks''
            ; kst := kst ks''
            |}*)
       ; hdlr_env := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (hdlr_env _ s'')
       |}
    | None   =>  hdlr_state_run_cmd envd s c2 (snd i)
    end
  end s input.

Fixpoint default_input {envd term} (c : cmd term envd) : s[[run_cmd_it c]] :=
  match c with
  | Spawn _ _ _ _ _ => devnull
  | Call _ _ _ _ _ => devnull
  | InvokeFD _ _ _ _ _ => devnull
  | InvokeStr _ _ _ _ _ => nil
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

Fixpoint get_non_null {envd term} (c : cmd term envd) :
  list (fin (projT1 envd)) :=
  match c with
  | Seq _ c1 c2 => (get_non_null c1) ++ (get_non_null c2)
  | Spawn _ _ _ i _ => i :: nil
  | Call _ _ _ i _ => i :: nil
  | InvokeFD _ _ _ i _ => i :: nil
  | _ => nil
  end.

Fixpoint payload_expr_non_null {envd term n} (non_null:list (fin (projT1 envd)))
  (expr_non_null:forall envd d, expr term envd d -> list (fin (projT1 envd)) -> bool) :
  forall (vd:vdesc' n), payload_expr' term envd n vd -> bool :=
  match n as _n return
    forall (_vd:vdesc' _n), payload_expr' term envd _n _vd -> bool
  with
  | 0 => fun _ _ => true
  | S n' => fun vd =>
    match vd as _vd return
      payload_expr' term envd (S n') _vd -> bool
    with
    | (d, vd') => fun p =>
      expr_non_null _ (Desc d) (fst p) non_null &&
      payload_expr_non_null non_null expr_non_null vd' (snd p)
    end
  end.

Fixpoint cmd_non_null {envd term} (c:cmd term envd) :
  (forall envd d, expr term envd d -> list (fin (projT1 envd)) -> bool) ->
  list (fin (projT1 envd)) -> bool :=
  match c in cmd _ _envd return
    (forall envd d, expr term envd d -> list (fin (projT1 envd)) -> bool) ->
    list (fin (projT1 _envd)) -> bool
  with
  | Nop _ => fun _ _ => true
  | Seq _ c1 c2 => fun expr_non_null non_null =>
    cmd_non_null c1 expr_non_null non_null &&
    cmd_non_null c2 expr_non_null (non_null ++ get_non_null c1)
  | Ite _ _ c1 c2 => fun expr_non_null non_null =>
    cmd_non_null c1 expr_non_null non_null &&
    cmd_non_null c2 expr_non_null non_null
  | Send _ _ e _ p => fun expr_non_null non_null =>
    expr_non_null _ _ e non_null &&
    payload_expr_non_null non_null expr_non_null _ p
  | Spawn _ _ p _ _ => fun expr_non_null non_null =>
    payload_expr_non_null non_null expr_non_null _ p
  | Call _ e le _ _ => fun expr_non_null non_null =>
    expr_non_null _ _ e non_null &&
    forallb (fun e => expr_non_null _ _ e non_null) le
  | InvokeFD _ e le _ _ => fun expr_non_null non_null =>
    expr_non_null _ _ e non_null &&
    forallb (fun e => expr_non_null _ _ e non_null) le
  | InvokeStr _ e le _ _ => fun expr_non_null non_null =>
    expr_non_null _ _ e non_null &&
    forallb (fun e => expr_non_null _ _ e non_null) le
  | StUpd _ _ e => fun expr_non_null non_null =>
    expr_non_null _ _ e non_null
  | CompLkup envd _ c1 c2 => fun expr_non_null non_null =>
    cmd_non_null c1 expr_non_null (max_fin (projT1 envd) :: map lift_fin non_null) &&
    cmd_non_null c2 expr_non_null non_null
  end.

Fixpoint base_term_non_null envd d (t:base_term envd d)
  (non_null:list (fin (projT1 envd))) : bool :=
  match t with
  | Var i =>
    projT1 (bool_of_sumbool (List.in_dec fin_eq_dec i non_null))
  | CompFd ct t' => base_term_non_null envd (Comp ct) t' non_null
  | _ => true
  end.

Fixpoint hdlr_term_non_null ct tag envd d (t:hdlr_term ct tag envd d)
  (non_null:list (fin (projT1 envd))) : bool :=
  match t with
  | Base d t' => base_term_non_null envd d t' non_null
  | CComp   => true
  | CConf _ _ t' => hdlr_term_non_null ct tag envd _ t' non_null
  | MVar _ => true
  | StVar _ => true
  end.

Fixpoint expr_non_null (term:vcdesc->cdesc->Set)
  (term_non_null:forall envd d, term envd d -> list (fin (projT1 envd)) -> bool)
  envd d (e:expr term envd d)
  (non_null:list (fin (projT1 envd))) : bool :=
  match e with
  | Term _ t => term_non_null envd _ t non_null
  | UnOp _ _ _ e' => expr_non_null term term_non_null envd _ e' non_null
  | BinOp _ _ _ _ e1 e2 =>
    expr_non_null term term_non_null envd _ e1 non_null &&
    expr_non_null term term_non_null envd _ e2 non_null
  end.

Definition base_expr_non_null :=
  expr_non_null _ base_term_non_null.

Definition hdlr_expr_non_null ct tag :=
  expr_non_null _ (hdlr_term_non_null ct tag).

Definition init_cmd_ok {envd} (c:cmd base_term envd)
  non_null :=
  cmd_non_null c base_expr_non_null non_null = true.

Definition hdlr_cmd_ok {envd} ct tag
  (c:cmd (hdlr_term ct tag) envd) non_null :=
  cmd_non_null c (hdlr_expr_non_null ct tag)
  non_null = true.

Fixpoint cmd_fins_assigned {envd} (c:cmd base_term envd)
  : list (fin KSTD_SIZE) :=
  match c with
  | Seq _ c1 c2 => set_union fin_eq_dec
    (cmd_fins_assigned c1) (cmd_fins_assigned c2)
  | Ite _ _ c1 c2 => set_inter fin_eq_dec
    (cmd_fins_assigned c1) (cmd_fins_assigned c2)
  | CompLkup _ _ c1 c2 => set_inter fin_eq_dec
    (cmd_fins_assigned c1) (cmd_fins_assigned c2)
  | StUpd _ i _ => i::nil
  | _ => nil
  end.

Definition cmd_assigns_all_st {envd} (c:cmd base_term envd) :=
  proj1_sig (bool_of_sumbool
    (forall_fin (fun i => in_dec fin_eq_dec i (cmd_fins_assigned c)))).

Definition init_prog envd :=
  sig (fun c:cmd base_term envd =>
    init_cmd_ok c nil /\ cmd_assigns_all_st c = true).

Definition hdlr_prog (ct : COMPT) (tag : fin NB_MSG) envd :=
  sig (fun c:cmd (hdlr_term ct tag) envd =>
    hdlr_cmd_ok ct tag c nil).

Definition kstate_run_prog envd (s : kstate) (p : hdlr_prog CT CTAG envd)
  (input : s[[run_cmd_it (proj1_sig p)]]) : kstate :=
  hdlr_kst envd (hdlr_state_run_cmd envd (default_hdlr_state s envd) (proj1_sig p) input).

End WITHIN_HANDLER.

Variable IENVD : vcdesc.

Variable IPROG : init_prog IENVD.

Definition initial_init_state :=
  {| init_comps := nil
   ; init_ktr   := [nil]%inhabited
   ; init_env   := default_cpayload IENVD
   ; init_kst   := default_cpayload KSTD
   |}.

Section WITH_HANDLER.

Definition handlers := forall (tag : fin NB_MSG) (ct : COMPT),
  sigT (fun prog_envd => hdlr_prog ct tag prog_envd).

Variable HANDLERS : handlers.

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
           s = init_state_run_cmd IENVD initial_init_state (proj1_sig IPROG) input ->
           InitialState input {| kcs := init_comps _ s
                               ; ktr := init_ktr _ s
                               ; kst := init_kst _ s
                               |}.

Definition mk_inter_ve_st c m s tr :=
  let cs := kcs s in
  {| kcs := cs
   ; ktr := [KRecv c m :: KSelect cs c :: tr]
   ; kst := kst s
   |}.

Inductive ValidExchange (c:comp) (m:msg)
  (input:sdenote_itt (run_cmd_it (proj1_sig (projT2 ((HANDLERS (tag m) (comp_type c)))))))
  : kstate -> kstate -> Prop :=
| C_ve : forall s tr s',
           let cs := kcs s in
           In c cs ->
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
   |}.

Inductive BogusExchange (c:comp) (bmsg:bogus_msg)
  : kstate -> kstate -> Prop :=
| C_be : forall s tr,
  let cs := kcs s in
  In c cs ->
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

Definition init_invariant {envd} (s : init_state envd)
  non_null_env non_null_st :=
  tr :~~ init_ktr _ s in
  let fds := trace_fds (expand_ktrace tr) in
  all_open fds
  * [all_comp_fds_in (init_comps _ s) fds]
  * [forall i, In i non_null_env ->
      in_if_fd_cdesc (init_env _ s) i fds]
  * [forall i, In i non_null_st ->
      in_if_fd_cdesc (init_kst _ s) i fds]
.

Definition hdlr_invariant {envd} (cc : comp) (cm : msg) (s : hdlr_state envd) non_null :=
  let st := hdlr_kst _ s in
  let env := hdlr_env _ s in
  tr :~~ ktr st in
  let fds := trace_fds (expand_ktrace tr) in
  all_open fds
  * [In cc (kcs st)]
  * [all_comp_fds_in (kcs st) fds]
  * [vcdesc_fds_all_in (kst st) fds]
  * [vdesc_fds_all_in (pay cm) fds]
  * [forall i, In i non_null ->
      in_if_fd_cdesc env i fds]
.

Definition kstate_inv s : hprop :=
(*  let fds := kfd s in*)
  tr :~~ ktr s in
  let fds := trace_fds (expand_ktrace tr) in
  traced (expand_ktrace tr)
  * all_open fds
  * [Reach s]
  * [all_comp_fds_in (kcs s) fds]
  * [vcdesc_fds_all_in (kst s) fds]
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
  | [ H1 : init_ktr _ ?s = [_]%inhabited, H2 : init_ktr _ ?s = [_]%inhabited |- _ ] =>
    rewrite H1 in H2; apply pack_injective in H2;
    rewrite -> H2 in * || rewrite <- H2 in * (* subst may be blocked *)
  | [ H : [?x]%inhabited = [?y]%inhabited |- _ ] =>
    apply pack_injective in H; try first [subst x | subst y]
  end.

Ltac get_input :=
  match goal with
  | [ |- exists _ : unit, _ ]
    => exists tt
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
  | [ f : fd |- exists i : fd, _ ]
    => exists f
  | [ s : str |- exists i : str, _ ]
    => exists s
  end.

Ltac misc :=
  match goal with
  | [ |- Reach _ ] => solve [econstructor; eauto]
  end.

Ltac unfoldr :=
  unfold kstate_inv, init_invariant, hdlr_invariant, CT, CTAG.

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

(*Lemma vcdesc_fds_subset_rest :
  forall fds RESTSIZE
         (PAY0: cdesc) (PAYREST: vcdesc' RESTSIZE) (e0: s[[PAY0]]) (erest: s[[PAYREST]]),
  vcdesc_fds_all_in (vd := existT vcdesc' (S RESTSIZE) (PAY0, PAYREST)) (e0, erest) fds ->
  vcdesc_fds_all_in (vd := existT vcdesc' _ PAYREST) erest fds.
Proof.
  unfold vcdesc_fds_all_in, vcdesc_fds.
  intros until 0. intros SUB.
  destruct PAY0 as []_eqn.
  destruct d as []_eqn; try easy.
  intros ? IN. apply SUB. simpl. now right.
  intros ? IN. apply SUB. simpl. now right.
Qed.

Lemma vcdesc_fds_lemma: forall envd (e : s[[envd]]) fds i,
  vcdesc_fds_subset (envd := envd) e fds ->
  match svec_ith (projT2 envd) i as __d return s[[__d]] -> Prop with
  | Desc d => match d as __d return s[[__d]] -> Prop with
              | fd_d => fun v => FdSet.In v fds
              | _    => fun _ => True
              end
  | Comp c => fun v => FdSet.In (comp_fd (projT1 v)) fds
  end (shvec_ith sdenote_cdesc (projT2 envd) e i).
Proof.
  unfold vcdesc_fds_subset, vcdesc_fds_set.
  intros [ENVD_SIZE ENVD]. induction ENVD_SIZE.
  intros. now exfalso.
  intros e fds i SUB.
  simpl in *. unfold sdenote_vcdesc in e. destruct ENVD as [ENVD0 ENVD].
  simpl in *. destruct e as [e0 e].
  destruct i as [i|].
  apply IHENVD_SIZE.
  intros x IN. apply SUB.
  destruct ENVD0.
  destruct d. assumption. assumption. apply FdSet.add_spec. now right.
  apply FdSet.add_spec. now right.
  destruct ENVD0. destruct d. exact I. exact I.
  apply SUB. apply FdSet.add_spec. now left.
  apply SUB. apply FdSet.add_spec. now left.
Qed.

Lemma vdesc_fds_lemma: forall vd (v : s[[vd]]) fds i,
  vdesc_fds_subset (envd := vd) v fds ->
  match svec_ith (projT2 vd) i as _d return s[[_d]] -> Prop with
  | fd_d => fun v => FdSet.In v fds
  | _    => fun _ => True
  end (shvec_ith sdenote_desc (projT2 vd) v i).
Proof.
  unfold vdesc_fds_subset, vdesc_fds_set.
  intros [VD_SIZE VD]. induction VD_SIZE.
  intros. now exfalso.
  intros v fds i SUB.
  simpl in *. unfold sdenote_vdesc in v. destruct VD as [VD0 VD].
  simpl in *. destruct v as [v0 v].
  destruct i as [i|].
  apply IHVD_SIZE.
  intros x IN. apply SUB.
  destruct VD0.
  assumption. assumption. apply FdSet.add_spec. now right.
  destruct VD0; auto.
  apply SUB. apply FdSet.add_spec. now left.
Qed.*)

(*base_expr_non_null envd (Comp ct) ce nn &&
        payload_expr_non_null nn base_expr_non_null (projT2 (lkup_tag t)) me*)

Lemma base_expr_fds_lemma' : forall envd (e : s[[envd]]) fds
  d (ce : expr base_term envd d) nn,
  base_expr_non_null envd d ce nn = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  match d as _d return s[[_d]] -> Prop with
  | Desc d => match d as _d return s[[Desc _d]] -> Prop with
              | fd_d => fun v => In v fds
              | _    => fun _ => True
              end
  | Comp c => fun v => comp_fds_in (projT1 v) fds
  end (eval_base_expr e ce).
Proof.
  intros envd e fds d ce nn Hok Hnn.
  destruct ce.
    unfold base_expr_non_null, base_term_non_null in Hok.
    unfold in_if_fd_cdesc in Hnn.
    simpl in Hok.
    induction b; simpl; auto.
      apply Hnn.
      destruct (in_dec fin_eq_dec i nn);
        auto; try discriminate.
        apply IHb; auto.

    destruct u; auto.
    destruct b; auto.
Qed.

Lemma base_expr_fds_lemma : forall envd (e : s[[envd]]) fds
  d (ce : expr base_term envd d) nn,
  base_expr_non_null envd d ce nn = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  match d as _d return s[[_d]] -> Prop with
  | Desc d => match d as _d return s[[Desc _d]] -> Prop with
              | fd_d => fun v => In v fds
              | _    => fun _ => True
              end
  | Comp c => fun v => In (comp_fd (projT1 v)) fds
  end (eval_base_expr e ce).
Proof.
  intros envd e fds d ce nn Hok Hnn.
  pose proof (base_expr_fds_lemma' envd e fds d ce nn Hok Hnn) as H'.
  unfold comp_fds_in in H'. destruct d; intuition.
Qed.

Lemma base_pl_expr_fds_sub : forall envd (e:sdenote_vcdesc envd) vd pe fds nn,
  payload_expr_non_null nn base_expr_non_null
    (projT2 vd) pe = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  vdesc_fds_all_in
    (eval_base_payload_expr envd e vd pe)
    fds.
Proof.
  intros envd e vd pe fds nn Hok Hnn.
  destruct vd as [n vd].
  induction n.
    unfold vdesc_fds_all_in. simpl. intuition.
  
    unfold vdesc_fds_all_in, in_if_fd_desc in *. destruct vd.
    unfold eval_base_payload_expr in *. destruct pe as [pe0 pe']. simpl in *.
    apply andb_prop in Hok. destruct Hok as [H1 H2].
    intro i; destruct i; destruct d; simpl in *; auto; try apply IHn; auto.
      eapply base_expr_fds_lemma with (e:=e) (ce:=pe0) (fds:=fds); eauto.
Qed.

Lemma hdlr_expr_fds_lemma' : forall cc cm envd (e:s[[envd]]) (st:s[[KSTD]]) fds
  d (ce : expr (hdlr_term (comp_type cc) (tag cm)) envd d) nn,
  hdlr_expr_non_null (comp_type cc) (tag cm) envd d ce nn = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  vdesc_fds_all_in (pay cm) fds ->
  vdesc_fds_all_in (comp_conf cc) fds ->
  vcdesc_fds_all_in st fds->
  In (comp_fd cc) fds ->
  match d as _d return s[[_d]] -> Prop with
  | Desc d => match d as _d return s[[Desc _d]] -> Prop with
              | fd_d => fun v => In v fds
              | _    => fun _ => True
              end
  | Comp c => fun v => comp_fds_in (projT1 v) fds
  end (eval_hdlr_expr cc cm st e ce).
Proof.
  intros cc cm envd e st fds d ce nn Hok Hnn Hsub_cm Hsub_cc Hsub_st Hcc_in.
  destruct ce. unfold comp_fds_in.
    induction h; simpl; auto.
      eapply base_expr_fds_lemma' with (e:=e) (ce:=Term _ _ b) (fds:=fds); eauto.
      destruct (eval_hdlr_term cc cm st h e) as [cp pf]_eqn. simpl.
      destruct pf. simpl in *. rewrite Heqs in IHh. simpl in *.
      apply IHh. unfold hdlr_expr_non_null in *. simpl in *. auto.

      apply Hsub_cm.
      apply Hsub_st.

    destruct u; auto.
    destruct b; auto.
Qed.

Lemma hdlr_expr_fds_lemma : forall cc cm envd (e:s[[envd]]) (st:s[[KSTD]]) fds
  d (ce : expr (hdlr_term (comp_type cc) (tag cm)) envd d) nn,
  hdlr_expr_non_null (comp_type cc) (tag cm) envd d ce nn = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  vdesc_fds_all_in (pay cm) fds ->
  vdesc_fds_all_in (comp_conf cc) fds ->
  vcdesc_fds_all_in st fds->
  In (comp_fd cc) fds ->
  match d as _d return s[[_d]] -> Prop with
  | Desc d => match d as _d return s[[Desc _d]] -> Prop with
              | fd_d => fun v => In v fds
              | _    => fun _ => True
              end
  | Comp c => fun v => In (comp_fd (projT1 v)) fds
  end (eval_hdlr_expr cc cm st e ce).
Proof.
  intros cc cm envd e st fds d ce nn Hok Hnn Hsub_cm Hsub_cc Hsub_st Hcc_in.
  pose proof (hdlr_expr_fds_lemma' cc cm envd e st fds d ce nn Hok Hnn
    Hsub_cm Hsub_cc Hsub_st Hcc_in) as H'. unfold comp_fds_in in H'.
  destruct d; intuition.
Qed.

Lemma hdlr_pl_expr_fds_sub : forall cc cm st envd
  (e:sdenote_vcdesc envd) vd pe fds nn,
  payload_expr_non_null nn (hdlr_expr_non_null (comp_type cc) (tag cm))
    (projT2 vd) pe = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  vdesc_fds_all_in (pay cm) fds ->
  vdesc_fds_all_in (comp_conf cc) fds ->
  vcdesc_fds_all_in st fds->
  In (comp_fd cc) fds ->
  vdesc_fds_all_in
    (eval_hdlr_payload_expr cc cm st envd e vd pe)
    fds.
Proof.
  intros cc cm st envd e vd pe fds nn Hok Hnn Hsub_cm Hsub_cc Hsub_st Hin_cc.
  unfold vdesc_fds_all_in, in_if_fd_desc.
  destruct vd as [n vd].
  induction n.
    unfold vdesc_fds_all_in. simpl in *. intuition.
  
    unfold vdesc_fds_all_in, in_if_fd_desc in *. destruct vd.
    unfold eval_hdlr_payload_expr. destruct pe as [pe0 pe']. simpl in *.
    apply andb_prop in Hok. destruct Hok as [H1 H2].
    intro i; destruct i; destruct d; simpl in *; auto; try apply IHn; auto.
      eapply hdlr_expr_fds_lemma with (e:=e) (ce:=pe0) (st:=st) (fds:=fds); eauto.
Qed.

Lemma shvec_ith_replace_ith :
  forall {desc sdenote_desc n} {vd:svec desc n} (v:shvec sdenote_desc vd) i e,
  shvec_ith sdenote_desc vd (shvec_replace_ith sdenote_desc vd v i e) i = e.
Proof.
  intros desc sdenote_desc n vd v i e.
  induction n.
    simpl in *; contradiction.
    
    destruct i; destruct vd as [d vd']; simpl in *; auto.
Qed.

Lemma shvec_ith_replace_other :
  forall {desc sdenote_desc n} {vd:svec desc n} (v:shvec sdenote_desc vd) i i' e,
  i <> i' ->
  shvec_ith sdenote_desc vd (shvec_replace_ith sdenote_desc vd v i e) i' =
  shvec_ith sdenote_desc vd v i'.
Proof.
  intros desc sdenote_desc n vd v i i' e Hneq.
  induction n.
    simpl in *; contradiction.
    
    destruct i'; destruct i; try discriminate;
    destruct vd; simpl in *;
      try solve [reflexivity |
        congruence | apply IHn; congruence].
Qed.

Lemma stupd_sub_hdlr : forall st (envd:vcdesc) (e:s[[envd]]) cc cm i ve fds nn,
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  hdlr_expr_non_null (comp_type cc) (tag cm) envd _ ve nn = true ->
  vcdesc_fds_all_in st fds ->
  vdesc_fds_all_in (pay cm) fds ->
  vdesc_fds_all_in (comp_conf cc) fds ->
  In (comp_fd cc) fds ->
  vcdesc_fds_all_in
    (shvec_replace_ith sdenote_cdesc _ st i (eval_hdlr_expr (envd:=envd) cc cm st e ve))
    fds.
Proof.
  intros st envd e cc cm i ve fds nn_e Hallin_e
    Hok Hsub_st Hsub_pay Hsub_cfg Hin_cc.
  unfold vcdesc_fds_all_in, in_if_fd_cdesc. intro i'.
  pose proof (fin_eq_dec i i') as Hfeq_dec.
  destruct Hfeq_dec as [Hfeq | Hfneq].
    rewrite <- Hfeq. rewrite shvec_ith_replace_ith.
    apply hdlr_expr_fds_lemma' with (nn:=nn_e); auto.

    rewrite shvec_ith_replace_other; auto.
    apply Hsub_st.
Qed.

Lemma in_if_fd_replace_st : forall envd st nn_st nn_e i i' fds
  (e:s[[envd]]) (ve:expr base_term envd (svec_ith KSTD_DESC i')),
  (forall i, In i nn_st -> in_if_fd_cdesc st i fds) ->
  (forall i, In i nn_e -> in_if_fd_cdesc e i fds) ->
  base_expr_non_null envd (svec_ith KSTD_DESC i') ve nn_e = true ->
  In i (set_add fin_eq_dec i' nn_st) ->
  in_if_fd_cdesc
    (shvec_replace_ith sdenote_cdesc KSTD_DESC st i'
      (eval_base_expr e ve))
    i fds.
Proof.
  intros envd st nn_st nn_e i i' fds e ve Hallin_st Hallin_e Hok Hin.
  unfold in_if_fd_cdesc.
  pose proof (fin_eq_dec i i') as Hfeq_dec.
  destruct Hfeq_dec as [Hfeq | Hfneq].
    subst i. rewrite shvec_ith_replace_ith.
    eapply base_expr_fds_lemma'; eauto.

    rewrite shvec_ith_replace_other; auto.
    apply set_add_elim in Hin; destruct Hin; try congruence.
    apply Hallin_st; auto.
Qed.

Lemma trace_fds_dist : forall tr1 tr2,
  trace_fds (tr1 ++ tr2) = trace_fds tr1 ++ trace_fds tr2.
Proof.
  intros tr1 tr2.
  induction tr1.
    auto.

    simpl. rewrite IHtr1. rewrite <- app_assoc. auto.
Qed.

Lemma trace_send_fds_empty : forall f m,
  trace_fds (trace_send_msg f m) = nil.
Proof.
  Local Transparent SendNum SendStr num_of_nat.
  intros f m.
  unfold trace_send_msg. unfold trace_payload_send.
  unfold trace_payload. (* unfold trace_payload'.*)
  destruct m as [t p]. simpl. destruct (lkup_tag t) as [n pd]. simpl.
  destruct (num_of_fin t).
  induction n.
    intuition.

    simpl in *. destruct pd. destruct p. simpl in *.
    destruct d; simpl in *; repeat rewrite app_ass; simpl in *;
    destruct s; simpl; erewrite <- IHn; repeat rewrite trace_fds_dist in *;
    simpl; eauto.
Qed.

Lemma trace_send_fds_equal : forall f m tr,
  trace_fds (trace_send_msg f m ++ tr) = trace_fds tr.
Proof.
  intros f m tr. rewrite trace_fds_dist.
  rewrite trace_send_fds_empty. auto.
Qed.

Lemma trace_send_fds : forall f m tr,
  all_open (trace_fds (trace_send_msg f m ++ tr)) <==> all_open (trace_fds tr).
Proof.
  intros f m tr. rewrite trace_send_fds_equal. auto.
Qed.

Lemma shvec_ith_replace_cast_ith :
  forall {d} {vd:vcdesc} (v:shvec sdenote_cdesc (projT2 vd)) i
    (EQ:svec_ith (projT2 vd) i = d) e,
  shvec_ith sdenote_cdesc (projT2 vd) (shvec_replace_cast EQ v e) i = 
  match EQ in _ = _d return s[[ _d ]] -> _ with Logic.eq_refl => fun x => x end e.
Proof.
  intros d vd v i EQ e.
  destruct vd as [n vd].
  induction n.
    simpl in *; contradiction.
    
    destruct i; destruct vd as [c vd']; simpl in *.
    destruct EQ. specialize (IHn vd' (snd v) f (Logic.eq_refl _)).
    simpl in IHn. auto.
    reflexivity.
Qed.

Lemma shvec_ith_replace_cast_other :
  forall {d} {vd:vcdesc} (v:shvec sdenote_cdesc (projT2 vd)) i i'
    (EQ:svec_ith (projT2 vd) i = d) e,
  i <> i' ->
  shvec_ith sdenote_cdesc (projT2 vd) (shvec_replace_cast EQ v e) i' =
  shvec_ith sdenote_cdesc (projT2 vd) v i'.
Proof.
  intros d vd v i i' EQ e Hneq.
  destruct vd as [n vd]. induction n.
    simpl in *; contradiction.
    
    destruct i'; destruct i; try discriminate;
    destruct vd; simpl in *;
      try solve [reflexivity |
        congruence | apply IHn; congruence].
Qed.

Lemma in_if_fd_desc_right' : forall d v f fds,
  match d as __d return (s[[__d]] -> Prop) with
  | num_d => fun _ : s[[num_d]] => True
  | str_d => fun _ : s[[str_d]] => True
  | fd_d => fun v : s[[fd_d]] => In v fds
  end v ->
  match d as __d return (s[[__d]] -> Prop) with
  | num_d => fun _ : s[[num_d]] => True
  | str_d => fun _ : s[[str_d]] => True
  | fd_d => fun v : s[[fd_d]] => In v (f :: fds)
  end v.
Proof.
  intros d v f fds Hin.
  destruct d; simpl; auto.
Qed.

Lemma in_if_fd_desc_right : forall n (vd:svec desc n) (v:s[[vd]]) i f fds,
  in_if_fd_desc v i fds -> in_if_fd_desc v i (f :: fds).
Proof.
  intros n vd v i f fds Hin.
  unfold in_if_fd_desc in *.
  eapply in_if_fd_desc_right' in Hin; eauto.
Qed.

Lemma vdesc_fds_sub : forall vd (v:s[[vd]]) f fds,
  vdesc_fds_all_in v fds ->
  vdesc_fds_all_in v (f::fds).
Proof.
  intros vd v f fds Hin.
  unfold vdesc_fds_all_in in *. intro i.
  apply in_if_fd_desc_right; auto.
Qed.

Lemma in_if_fd_cdesc_right' : forall c v f fds,
  match c as __d return (s[[__d]] -> Prop) with
  | Desc d =>
    match d as __d return (s[[__d]] -> Prop) with
    | num_d => fun _ : s[[num_d]] => True
    | str_d => fun _ : s[[str_d]] => True
    | fd_d => fun v : s[[fd_d]] => In v fds
    end
  | Comp c => fun v : s[[Comp c]] => comp_fds_in (projT1 v) fds
  end v ->
  match c as __d return (s[[__d]] -> Prop) with
  | Desc d =>
    match d as __d return (s[[__d]] -> Prop) with
    | num_d => fun _ : s[[num_d]] => True
    | str_d => fun _ : s[[str_d]] => True
    | fd_d => fun v : s[[fd_d]] => In v (f :: fds)
    end
  | Comp c => fun v : s[[Comp c]] => comp_fds_in (projT1 v) (f :: fds)
  end v.
Proof.
  intros c v f fds Hin.
  destruct c as [d | c].
    destruct d; simpl; auto.

    unfold comp_fds_in in *. split.
      simpl; tauto.

      apply vdesc_fds_sub; tauto.
Qed.

Lemma in_if_fd_cdesc_right : forall n (vd:svec cdesc n) (v:s[[vd]]) i f fds,
  in_if_fd_cdesc v i fds -> in_if_fd_cdesc v i (f :: fds).
Proof.
  intros n vd v i f fds Hin.
  unfold in_if_fd_cdesc in *.
  eapply in_if_fd_cdesc_right' in Hin; eauto.
Qed.

Lemma vcdesc_fds_sub : forall vd (v:s[[vd]]) f fds,
  vcdesc_fds_all_in v fds ->
  vcdesc_fds_all_in v (f::fds).
Proof.
  intros vd v f fds Hin.
  unfold vcdesc_fds_all_in in *. intro i.
  apply in_if_fd_cdesc_right; auto.
Qed.

Lemma in_if_fd_replace_comp : forall ct envd i
  (EQ:svec_ith (projT2 envd) i = Comp ct) e c_fd cfg fds i' nn,
  vdesc_fds_all_in cfg fds ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  In i' (nn ++ i :: nil) ->
  in_if_fd_cdesc
    (shvec_replace_cast EQ e
      (existT (fun c1 : comp => comp_type c1 = ct) 
        {|comp_type:=ct; comp_fd:=c_fd; comp_conf:=cfg|}
        (Logic.eq_refl ct))) i'
    (c_fd :: fds).
Proof.
  intros ct envd i EQ e c_fd cfg fds i' nn
    Hcfg Hall_in Hnn.
  unfold in_if_fd_cdesc.
  pose proof (fin_eq_dec i i') as Hfeq_dec.
  destruct Hfeq_dec as [Hfeq | Hfneq].
    rewrite <- Hfeq in *. rewrite shvec_ith_replace_cast_ith.
    unfold vcdesc'. rewrite EQ. unfold comp_fds_in. split.
      simpl. left. auto.

      simpl. apply vdesc_fds_sub; auto.

    rewrite shvec_ith_replace_cast_other; auto.
    apply in_if_fd_cdesc_right; auto.
    apply (Hall_in i'). apply in_app_or in Hnn.
    destruct Hnn; auto. destruct H; intuition congruence.
Qed.

Lemma in_if_fd_replace_fd : forall envd i
  (EQ:svec_ith (projT2 envd) i = Desc fd_d) e f fds i' nn,
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  In i' (nn ++ i :: nil) ->
  in_if_fd_cdesc
      (shvec_replace_cast EQ e f) i'
      (f :: fds).
Proof.
  intros envd i EQ e f fds i' nn Hall_in Hnn.
  unfold in_if_fd_cdesc.
  pose proof (fin_eq_dec i i') as Hfeq_dec.
  destruct Hfeq_dec as [Hfeq | Hfneq].
    rewrite <- Hfeq in *. rewrite shvec_ith_replace_cast_ith.
    unfold vcdesc'. rewrite EQ. simpl. left. auto.

    rewrite shvec_ith_replace_cast_other; auto.
    apply in_if_fd_cdesc_right; auto.
    apply (Hall_in i'). apply in_app_or in Hnn.
    destruct Hnn; auto. destruct H; intuition congruence.
Qed.

Lemma in_if_fd_replace_not_fd : forall envd i d
  (EQ:svec_ith (projT2 envd) i = Desc d) e f fds i' nn,
  d <> fd_d ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  In i' nn ->
  in_if_fd_cdesc
      (shvec_replace_cast EQ e f) i'
      fds.
Proof.
  intros envd i d EQ e f fds i' nn Hnot_fd Hall_in.
  unfold in_if_fd_cdesc.
  pose proof (fin_eq_dec i i') as Hfeq_dec.
  destruct Hfeq_dec as [Hfeq | Hfneq].
    rewrite <- Hfeq in *. rewrite shvec_ith_replace_cast_ith.
    unfold vcdesc'. rewrite EQ. destruct d; intuition.

    rewrite shvec_ith_replace_cast_other; auto.
    apply Hall_in.
Qed.

Lemma find_comp_suc : forall envd e cp cs c,
  find_comp (eval_base_comp_pat envd e cp) cs = Some c ->
  In (projT1 c) cs.
Proof.
  intros envd e cp cs c.
  induction cs.
    discriminate.

    simpl.
    match goal with
    |- context[ match ?e with Some _ => _ | None => _ end ]
      => destruct e
    end.
      intro H. inversion H. subst c. auto.

      auto.
Qed.

Lemma find_comp_suc_hdlr : forall cc cm envd env st cp cs c,
  find_comp (eval_hdlr_comp_pat cc cm st envd env cp) cs = 
    Some c ->
  In (projT1 c) cs.
Proof.
  intros cc cm envd env st cp cs c.
  induction cs.
    discriminate.

    simpl.
    match goal with
    |- context[ match ?e with Some _ => _ | None => _ end ]
      => destruct e
    end.
      intro H. inversion H. subst c. auto.

      auto.
Qed.

Lemma all_comp_fds_in_sub : forall cs f fds,
  all_comp_fds_in cs fds ->
  all_comp_fds_in cs (f :: fds).
Proof.
  intros cs f fds Hall_in.
  unfold all_comp_fds_in in *.
  intros c Hin. specialize (Hall_in c Hin).
  split.
    right; apply Hall_in.
    apply vdesc_fds_sub; apply Hall_in.
Qed.

Lemma vcdesc_fds_all_in_suf_ind : forall n (vd0:cdesc) (vd:svec cdesc n) (v0:s[[vd0]])
  (v:shvec sdenote_cdesc vd) fds,
  in_if_fd_cdesc (n:=S n) (vd:=(vd0, vd)) (v0, v) None fds ->
  vcdesc_fds_all_in (vd:=existT _ n vd) v fds ->
  vcdesc_fds_all_in (vd:=existT _ (S n) (vd0, vd)) (v0, v) fds.
Proof.
  intros n vd0 vd v0 v fds Hin Hall_in.
  unfold vcdesc_fds_all_in, in_if_fd_cdesc in *.
  intro i; destruct i; simpl in *;
    solve [ auto | apply Hall_in ].
Qed.

Lemma vcdesc_fds_all_in_rest : forall n (vd0:cdesc)
  (vd:svec cdesc n) (v0:s[[vd0]]) (v:s[[vd]]) fds,
  vcdesc_fds_all_in (vd:=existT _ (S n) (vd0, vd)) (v0, v) fds ->
  vcdesc_fds_all_in (vd:=existT _ n vd) v fds.
Proof.
  intros n vd0 vd v0 v fds Hall_in.
  intro i. specialize (Hall_in (Some i)).
  unfold in_if_fd_cdesc in *; simpl in *.
  auto.
Qed.

Fixpoint decr_fin_list {n} (l:list (fin (S n))) : list (fin n) :=
  match l with
  | nil => nil
  | None :: l' => decr_fin_list l'
  | Some f :: l' => f :: decr_fin_list l'
  end.

Lemma decr_fin_list_inv : forall n (l:list (fin (S n))) f,
  In f (decr_fin_list l) <-> In (Some f) l.
Proof.
  intros n l.
  induction l.
    intros; split; intros; contradiction.

    destruct a; simpl in *.
      intuition. left. f_equal. auto.
      right. apply IHl; auto.
      left. congruence.
      right. apply IHl; auto.
      intros; split; intuition.
      right. apply IHl; auto.
      discriminate.
      apply IHl; auto.
Qed.

Lemma map_decr_fin_list : forall n (l:list (fin (S n))),
  map lift_fin (decr_fin_list l) = decr_fin_list (map lift_fin l).
Proof.
  intros n l.
  induction l.
    reflexivity.

    destruct a; simpl; f_equal; auto.
Qed.

Lemma max_fin_in_shift : forall ct envd (e:sdenote_vcdesc envd) c fds,
  comp_fds_in (projT1 c) fds ->
  in_if_fd_cdesc
    (shvec_shift sdenote_cdesc (Comp ct) c (projT2 envd) e) (max_fin (projT1 envd)) fds.
Proof.
  intros ct envd e c fds Hc.
  destruct envd as [n envd'].
  induction n.
    simpl in *; intuition.

    destruct envd' as [d rest]. simpl. destruct e.
      simpl in *. apply IHn; congruence.
Qed.

Lemma fds_all_in_shift : forall ct envd (e:sdenote_vcdesc envd) c fds i nn,
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  In i (map lift_fin nn) ->
  i <> max_fin (projT1 envd) ->
  in_if_fd_cdesc
    (shvec_shift sdenote_cdesc (Comp ct) c (projT2 envd) e) i fds.
Proof.
  intros ct envd e c fds i nn Hall_in Hin Hmax.
  destruct envd as [n envd'].
  induction n.
    destruct i; simpl in *; intuition.

    destruct envd' as [d rest]. simpl. destruct e.
    destruct d as [d | cp].
    destruct i; destruct d; simpl in *; auto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply decr_fin_list_inv; auto.
      rewrite map_decr_fin_list.
      eapply decr_fin_list_inv with (l:=map (@lift_fin (S n)) nn); eauto.
      intuition. apply Hmax. subst f. auto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply decr_fin_list_inv; auto.
      rewrite map_decr_fin_list.
      eapply decr_fin_list_inv with (l:=map (@lift_fin (S n)) nn); eauto.
      intuition. apply Hmax. subst f. auto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply decr_fin_list_inv; auto.
      rewrite map_decr_fin_list.
      eapply decr_fin_list_inv with (l:=map (@lift_fin (S n)) nn); eauto.
      intuition. apply Hmax. subst f. auto.
      unfold in_if_fd_cdesc; simpl.
      apply (Hall_in None).
      pose proof (in_map_iff (@lift_fin (S n)) nn None).
      destruct H. specialize (H Hin). destruct H. destruct H.
      destruct x; simpl in *; auto; discriminate.
    destruct i; simpl in *.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply decr_fin_list_inv; auto.
      rewrite map_decr_fin_list.
      eapply decr_fin_list_inv with (l:=map (@lift_fin (S n)) nn); eauto.
      intuition. apply Hmax. subst f. auto.
      unfold in_if_fd_cdesc; simpl.
      apply (Hall_in None).
      pose proof (in_map_iff (@lift_fin (S n)) nn None).
      destruct H. specialize (H Hin). destruct H. destruct H.
      destruct x; simpl in *; auto; discriminate.
Qed.

Lemma lift_fin_not_max : forall n (f:fin n),
 lift_fin f <> max_fin n.
Proof.
  intros n f.
  induction n.
    contradiction.
    simpl. destruct f; auto. congruence.
    congruence.
Qed.

Lemma fds_all_in_unshift : forall c envd
  (e:shvec sdenote_cdesc (svec_shift c (projT2 envd))) fds nn i,
  (forall i, In i (map lift_fin nn) -> in_if_fd_cdesc e i fds) ->
  In i nn ->
  in_if_fd_cdesc
    (shvec_unshift cdesc sdenote_cdesc (projT1 envd) c 
      (projT2 envd) e) i fds.
Proof.
  intros c envd e fds nn i Hall_in Hin.
  destruct envd as [n envd'].
  induction n.
    destruct i; simpl in *; intuition.

    destruct envd' as [d rest]. simpl. destruct e.
    simpl in *. destruct i; repeat destruct d; simpl in *; auto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply (decr_fin_list_inv _ (map (@lift_fin (S n)) nn) i'); auto.
      rewrite <- map_decr_fin_list. auto.
      eapply decr_fin_list_inv; eauto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply (decr_fin_list_inv _ (map (@lift_fin (S n)) nn) i'); auto.
      rewrite <- map_decr_fin_list. auto.
      eapply decr_fin_list_inv; eauto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply (decr_fin_list_inv _ (map (@lift_fin (S n)) nn) i'); auto.
      rewrite <- map_decr_fin_list. auto.
      eapply decr_fin_list_inv; eauto.
      apply IHn with (nn:=decr_fin_list nn).
      intros i' H. apply (Hall_in (Some i')).
      apply (decr_fin_list_inv _ (map (@lift_fin (S n)) nn) i'); auto.
      rewrite <- map_decr_fin_list. auto.
      eapply decr_fin_list_inv; eauto.
      unfold in_if_fd_cdesc; simpl.
      apply (Hall_in None).
      apply (in_map (@lift_fin (S n)) nn None); auto.
      unfold in_if_fd_cdesc; simpl.
      apply (Hall_in None).
      apply (in_map (@lift_fin (S n)) nn None); auto.
Qed.

Lemma all_comp_fds_in_app_base :
  forall envd (e:s[[envd]]) ct c_fd
    cfge cs fds nn,
  let cfg := eval_base_payload_expr envd e (comp_conf_desc ct) cfge in
  let c:= {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  payload_expr_non_null nn base_expr_non_null
    _ cfge = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  all_comp_fds_in cs fds ->
  all_comp_fds_in (c :: cs) (c_fd :: fds).
Proof.
  intros envd e ct c_fd cfge cs fds nn cfg c Hok Hnn Hallc_in.
  unfold c. unfold cfg.
  intros c' Hin.
  destruct Hin.
    subst c'; simpl. split.
      left; auto.
      eapply base_pl_expr_fds_sub; eauto.
      intros. apply in_if_fd_cdesc_right. auto.

  split.
    right. apply Hallc_in; auto.

    apply vdesc_fds_sub; apply Hallc_in; auto.
Qed.

Lemma comp_in_cs : forall c cs fds,
  In c cs ->
  all_comp_fds_in cs fds ->
  comp_fds_in c fds.
Proof.
  intros c cs fds Hin Hall_in.
  specialize (Hall_in c Hin).
  intuition.
Qed.

Lemma all_comp_fds_in_app_hdlr :
  forall envd (e:s[[envd]]) ct c_fd cc cm st
    cfge cs fds nn,
  let cfg := eval_hdlr_payload_expr cc cm st envd e (comp_conf_desc ct) cfge in
  let c:= {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  payload_expr_non_null nn (hdlr_expr_non_null (comp_type cc) (tag cm))
    _ cfge = true ->
  (forall i, In i nn -> in_if_fd_cdesc e i fds) ->
  vdesc_fds_all_in (pay cm) fds ->
  vcdesc_fds_all_in st fds ->
  all_comp_fds_in cs fds ->
  In cc cs ->
  all_comp_fds_in (c :: cs) (c_fd :: fds).
Proof.
  intros envd e ct c_fd cc cm st cfge cs fds nn cfg c
    Hok Hnn Hin_pay Hin_st Hin_cs Hin_cc.
  unfold all_comp_fds_in.
  intros c' Hin. destruct Hin.
  subst c'; simpl. split.
    left; auto.
    unfold c, cfg. simpl.
    eapply hdlr_pl_expr_fds_sub; eauto.
    intros; apply in_if_fd_cdesc_right; auto.
    apply vdesc_fds_sub; auto.
    apply vdesc_fds_sub; auto.
    eapply comp_in_cs; eauto.
    apply vcdesc_fds_sub; auto.
    simpl. right.
    eapply comp_in_cs; eauto.

  split.
    right. apply Hin_cs; auto.

    apply vdesc_fds_sub; apply Hin_cs; auto.
Qed.

Ltac destruct_eq :=
  match goal with
  | [ |- context[ if ?e then _ else _ ] ] =>
    match e with
    | num_eq _ _ => destruct e
    end
  end.

(*It seems that you can't give ltac variables the same names as
  bound variables in lemmas. This is why I named the variables things
  like ce_in instead of ce.*)
Ltac fd_exprs_in :=
  match goal with
  | [ |- In (comp_fd ?c) ?fds_in ]
    => try subst c; simpl;
        match goal with
        | [ nn_in : list (fin _)
          |- In (comp_fd (projT1 (eval_base_expr ?e_in ?ce_in))) fds_in ]
          => apply base_expr_fds_lemma with
              (ce:=ce_in) (e:=e_in) (fds:=fds_in) (nn:=nn_in)
        | [ _ : In ?cc_in ?cs_in, nn_in : list (fin _)
          |- In (comp_fd (projT1 (eval_hdlr_expr ?cc_in ?cm_in ?st_in ?e_in ?ce_in))) fds_in ]
          => apply hdlr_expr_fds_lemma with
            (cc:=cc_in) (cm:=cm_in) (st:=st_in) (e:=e_in)
            (ce:=ce_in) (fds:=fds_in) (nn:=nn_in); auto; try apply comp_in_cs with (cs:=cs_in)
        | [ ocdp := find_comp _ _,
            Hall_in : all_comp_fds_in _ _ |- In (comp_fd _) fds_in ]
          => apply Hall_in; (eapply find_comp_suc ||
               eapply find_comp_suc_hdlr)
        | [ _ : context [ find_comp _ _ ],
            Hall_in : all_comp_fds_in _ _ |- In (comp_fd _) fds_in ]
          => apply Hall_in; (eapply find_comp_suc ||
               eapply find_comp_suc_hdlr)
        end
  end.

Ltac subst_states :=
  repeat match goal with
         | [ s : init_state _ |- _ ]
           => subst s
         | [ s : hdlr_state _ |- _ ]
           => subst s
         end; simpl in *.

Ltac find_comp_rewrite :=
  try match goal with
      | [ ocdp := find_comp _ _ |- _ ]
        => unfold ocdp in *
      end;
  match goal with
  | [ Heqo : find_comp _ _ = _ |- _ ]
    => rewrite Heqo
  end.

Ltac comp_fds_in :=
  match goal with
  | [ |- comp_fds_in ?c _ ]
    => unfold c;
    match goal with
    | [ _ : find_comp _ _ = Some _,
      H : all_comp_fds_in _ _ |- comp_fds_in (projT1 ?cdp) _ ]
      => apply H; eapply find_comp_suc with (c:=cdp); eauto
    end
  end.

Ltac set_in_dec_hyps :=
  repeat (unfold set_In in *;
    match goal with
    | [ H : In _ (set_union _ _ _) |- _ ]
      => apply set_union_elim in H;
         destruct H
    | [ H : In _ (set_inter _ _ _) |- _ ]
      => apply set_inter_elim in H;
         destruct H
    end).

Ltac set_in_dec_goal :=
  repeat (unfold set_In in *;
    match goal with
    | [ |- In _ (set_union _ _ _) ]
      => apply set_union_intro;
         solve
           [right; set_in_dec_goal; auto
           | left; set_in_dec_goal; auto]
    | [ |- In _ (set_inter _ _ _) ]
      => apply set_inter_intro
    end; auto).

Ltac set_in_dec :=
set_in_dec_hyps; set_in_dec_goal.

Hint Rewrite app_assoc : list.
Ltac in_if_fd_cdesc_non_null :=
  match goal with
  | [ H : forall i : fin _, In i _ -> in_if_fd_cdesc _ i _
    |- in_if_fd_cdesc _ _ _ ]
    => try apply in_if_fd_cdesc_right; apply H;
       solve [ autorewrite with list in *; auto with datatypes v62
             | set_in_dec ]
  end.

Ltac simplr_base :=
  subst_states;
  try uninhabit;
  discharge_pure;
  try get_input;
  try (now destruct_eq);
  try rewrite trace_send_fds_equal;
  try apply unpack_all_open;
  try apply repack_all_open;
  try fd_exprs_in;
  try solve [eapply all_comp_fds_in_app_base; eauto];
  try solve [eapply all_comp_fds_in_app_hdlr; eauto];
  try eapply in_if_fd_replace_comp; eauto;
  try eapply in_if_fd_replace_fd; eauto;
  try solve [eapply in_if_fd_replace_not_fd;
    eauto; autorewrite with list in *;
      auto; congruence];
  try solve [apply vcdesc_fds_sub; auto];
  try solve [apply all_comp_fds_in_sub; auto];
  try solve [eapply in_if_fd_replace_st; eauto];
  try eapply stupd_sub_hdlr; eauto;
  try solve [apply vdesc_fds_sub; auto];
  try solve [eapply base_pl_expr_fds_sub; eauto];
  try eapply hdlr_pl_expr_fds_sub; eauto;
  try solve [comp_fds_in];
  try find_comp_rewrite;
  try solve [in_if_fd_cdesc_non_null];
  try eapply comp_in_cs; eauto.

Record init_cmd_non_nulls {envd c} :=
  { nn_env : list (fin (projT1 envd));
    nn_st  : list (fin KSTD_SIZE);
    env_ok : init_cmd_ok c nn_env }.

Definition run_init_cmd :
  forall (envd : vcdesc) (s : init_state envd)
         (c : cmd base_term envd)
         (cmd_ok : @init_cmd_non_nulls envd c),
  STsep (tr :~~ init_ktr envd s in
          init_invariant s (nn_env cmd_ok) (nn_st cmd_ok)
          * traced (expand_ktrace tr))
        (fun s' : init_state envd => tr :~~ init_ktr envd s' in
          init_invariant s' (nn_env cmd_ok ++ get_non_null c)
            (set_union fin_eq_dec (nn_st cmd_ok) (cmd_fins_assigned c))
          * traced (expand_ktrace tr) *
          [exists i, s' = init_state_run_cmd envd s c i]).
Proof.
  intros envd sinit cinit okinit;
  refine (Fix4
    (fun envd c s ok => tr :~~ init_ktr envd s in
      init_invariant s (nn_env ok) (nn_st ok)
      * traced (expand_ktrace tr))
    (fun envd c s ok (s' : init_state envd) =>
      tr :~~ init_ktr envd s' in
      init_invariant s' (nn_env ok ++ get_non_null c)
        (set_union fin_eq_dec (nn_st ok) (cmd_fins_assigned c))
      * traced (expand_ktrace tr) *
      [exists i, s' = init_state_run_cmd envd s c i])
    (fun self envd0 c0 s0 ok => _) envd cinit sinit okinit
  ).
  clear cinit sinit okinit envd HANDLERS IPROG IENVD.
  refine (
    match 
      c0 as _c0 in cmd _ _envd0 return
      forall (_s0 : init_state _envd0)
        (_ok : @init_cmd_non_nulls _envd0 _c0),
         STsep
           (tr0 :~~ init_ktr _envd0 _s0 in
               init_invariant _s0 (nn_env _ok) (nn_st _ok)
               * traced (expand_ktrace tr0))
         (fun s' : init_state _envd0 =>
           tr' :~~ init_ktr _envd0 s' in
           init_invariant s' (nn_env _ok ++ get_non_null _c0)
             (set_union fin_eq_dec (nn_st _ok) (cmd_fins_assigned _c0))
           * traced (expand_ktrace tr') *
           [exists i, s' = init_state_run_cmd _envd0 _s0 _c0 i])
    with

    | Nop _ => fun s ok => {{ Return s }}

    | Seq envd c1 c2 => fun s ok =>
      let case := "Seq envd c1 c2"%string in _

    | Ite envd cond c1 c2 => fun s ok =>
      let case := "Ite envd cond c1 c2"%string in _

    | Send _ ct ce t me => fun s ok =>
      let case := "Send _ ct ce t me"%string in _

    | Spawn _ ct cfge i EQ => fun s ok =>
      let case := "Spawn _ ct cfg i EQ"%string in _

    | Call _ ce argse i EQ => fun s ok =>
      let case := "Call _ ce argse i EQ"%string in _

    | InvokeFD _ ce argse i EQ => fun s ok =>
      let case := "InvokeFD _ ce argse i EQ"%string in _

    | InvokeStr _ ce argse i EQ => fun s ok =>
      let case := "InvokeStr _ ce argse i EQ"%string in _

    | StUpd _ i ve => fun s ok =>
      let case := "StUpd _ i ve"%string in _

    | CompLkup envd cp c1 c2 => fun s ok =>
      let case := "CompLkup envd cp c1 c2"%string in _

    end s0 ok
  ); sep unfoldr simplr_base.

(* Seq *)
destruct ok0 as [nn_e nn_s ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
refine (
  s1 <- self envd c1 s {|nn_env:=nn_e;nn_st:=nn_s;env_ok:=H1|};
  s2 <- self envd c2 s1 {|nn_env:=nn_e ++ get_non_null c1;
    nn_st:=set_union fin_eq_dec nn_s (cmd_fins_assigned c1); env_ok:=H2|}
    <@> [exists i, s1 = init_state_run_cmd envd s c1 i];
  {{ Return s2 }}
); sep unfoldr simplr_base.

(* Ite *)
destruct ok0 as [nn_e nn_s ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
refine (
  if num_eq (eval_base_expr (init_env _ s) cond) FALSE
  then s' <- self envd c2 s {|nn_env:=nn_e;nn_st:=nn_s;env_ok:=H2|};
       {{ Return s' }}
  else s' <- self envd c1 s {|nn_env:=nn_e;nn_st:=nn_s;env_ok:=H1|};
       {{ Return s' }}
); sep unfoldr simplr_base.

(* Send *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as Hok.
destruct Hok as [Hok1 Hok2].
refine (
  let c := projT1 (eval_base_expr e ce) in
  let m := eval_base_payload_expr _ e _ me in
  let msg := Build_msg t m in
  send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ let fds := trace_fds (expand_ktrace tr) in
         all_open_drop fds (comp_fd c)
         * [all_comp_fds_in cs fds]
         * [forall i, In i nn_e ->
           in_if_fd_cdesc (init_env _ s) i fds]
         * [forall i, In i nn_st ->
           in_if_fd_cdesc (init_kst _ s) i fds]);;
  let tr := tr ~~~ KSend c msg :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := e
             ; init_kst   := st
             |}
  }}
); sep unfoldr simplr_base.

(* Spawn *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
refine (
  let c_cmd := compd_cmd (COMPS ct) in
  let c_args := compd_args (COMPS ct) in
  let cfg := eval_base_payload_expr _ e _ cfge in
  c_fd <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
      <@> init_invariant s nn_e nn_st;

  let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  let tr := tr ~~~ KExec c_cmd c_args c :: tr in
  {{ Return {| init_comps := c :: cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e (existT _ c (Logic.eq_refl ct))
             ; init_kst   := st
             |}
  }}
); sep unfoldr simplr_base.

(* Call *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
refine (
  let c := eval_base_expr e ce in
  let args := map (eval_base_expr e) argse in
  f <- call c args (tr ~~~ expand_ktrace tr)
   <@> init_invariant s nn_e nn_st;

  let tr := tr ~~~ KCall c args f :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e f
             ; init_kst   := st
             |}
  }}
); sep unfoldr simplr_base.

(* InvokeFD *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
refine (
  let c := eval_base_expr e ce in
  let args := map (eval_base_expr e) argse in
  f <- invoke_fd c args (tr ~~~ expand_ktrace tr)
   <@> init_invariant s nn_e nn_st;

  let tr := tr ~~~ KInvokeFD c args f :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e f
             ; init_kst   := st
             |}
  }}
); sep unfoldr simplr_base.

(* InvokeStr *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
refine (
  let c := eval_base_expr e ce in
  let args := map (eval_base_expr e) argse in
  res <- invoke_str c args (tr ~~~ expand_ktrace tr)
   <@> init_invariant s nn_e nn_st;

  let tr := tr ~~~ KInvokeStr c args res :: tr in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := shvec_replace_cast EQ e res
             ; init_kst   := st
             |}
  }}
); sep unfoldr simplr_base.

(* StUpd *)
destruct s as [cs tr e st fds]_eqn; simpl.
destruct ok0 as [nn_e nn_st ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
refine (
  let v := eval_base_expr e ve in
  {{ Return {| init_comps := cs
             ; init_ktr   := tr
             ; init_env   := e
             ; init_kst   := shvec_replace_ith _ _ st i v
             |}
  }}
); sep unfoldr simplr_base.

(* CompLkup *)
destruct s as [cs tr e st]_eqn; simpl.
destruct ok0 as [nn_e nn_s ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
pose (ocdp := find_comp (eval_base_comp_pat _ e cp) cs).
destruct ocdp as [ cdp | ]_eqn.
(*Component found*)
refine (
  let c := projT1 cdp in
  let d := Comp (comp_pat_type _ _ cp) in
  let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
  let s' := Build_init_state new_envd cs tr
    (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
      (existT _ c (projT2 cdp)) (projT2 envd) e)
  st in
  s'' <- self new_envd c1 s'
    (Build_init_cmd_non_nulls new_envd c1
      (max_fin (projT1 envd) ::
        (map lift_fin nn_e)) nn_s H1);
  {{ Return {| init_comps := init_comps _ s''
             ; init_ktr   := init_ktr _ s''
             ; init_env   := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (init_env _ s'')
             ; init_kst   := init_kst _ s''
             |}
  }}
); sep unfoldr simplr_base.
apply max_fin_in_shift; auto.
unfold c; apply H; eapply find_comp_suc with (c:=cdp); eauto.
eapply fds_all_in_shift; eauto.
pose proof (in_map_iff lift_fin nn_e i).
destruct H4. specialize (H4 H5). destruct H4. destruct H4.
rewrite <- H4. apply lift_fin_not_max.
eapply fds_all_in_unshift; eauto.
intros. apply H4. right.
autorewrite with list in *. auto with datatypes v62.

(*Component not found*)
refine (
  s' <- self envd c2 s {|nn_env:=nn_e;nn_st:=nn_s;env_ok:=H2|};
  {{ Return s' }}
); sep unfoldr simplr_base.
Qed.

Theorem all_open_concat : forall a b,
  all_open a * all_open b ==> all_open (a ++ b).
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
Qed.

Ltac init_st_assigned :=
  match goal with
  | [ H : forall i, In i _ -> in_if_fd_cdesc _ _ _ |- _ ]
    => unfold vcdesc_fds_all_in; intros; apply H;
       apply set_union_intro2;
       let st_ok := fresh "st_ok" in
       destruct IPROG as [? [? st_ok] ];
       simpl in *; unfold cmd_assigns_all_st in st_ok;
       match type of st_ok with
       | context [ bool_of_sumbool ?x ] =>
         destruct x; try discriminate; simpl in *;
         unfold set_In; auto
       end
  end.

Ltac init_constr :=
  match goal with
  | [ H : exists i : _, _ = _ |- _ ]
    => let i := fresh "i" in
       let Hin := fresh "Hin" in
       destruct H as [i Hin];
       eapply Reach_init with (input:=i);
       eauto
  end;
  econstructor; eauto.

Ltac unfoldr_init :=
  unfoldr;
  unfold all_comp_fds_in.

Ltac simplr_init :=
  discharge_pure;
  try solve [init_st_assigned];
  try solve [init_constr].

Definition kinit :
  forall (_ : unit),
  STsep (traced nil)
        (fun s => kstate_inv s).
Proof.
  intros; refine (
    let s := initial_init_state in
    s' <- run_init_cmd _ s (proj1_sig IPROG)
      {|nn_env:=nil;nn_st:=nil;env_ok:=proj1 (proj2_sig IPROG)|};
    {{ Return {| kcs := init_comps _ s'
               ; ktr := init_ktr _ s'
               ; kst := init_kst _ s'
               |}
     }}
  ); sep unfoldr_init simplr_init.
Qed.

Definition run_hdlr_cmd :
  forall (cc : comp) (cm : msg) (envd : vcdesc) (s : hdlr_state envd)
         (c : cmd (hdlr_term (comp_type cc) (tag cm)) envd)
         (cmd_ok:sigT (fun non_null:list (fin (projT1 envd)) =>
           hdlr_cmd_ok (comp_type cc) (tag cm) c non_null)),
  STsep (tr :~~ ktr (hdlr_kst _ s) in
          hdlr_invariant cc cm s (projT1 cmd_ok)
          * traced (expand_ktrace tr))
        (fun s' : hdlr_state envd => tr :~~ ktr (hdlr_kst _ s') in
          hdlr_invariant cc cm s' (projT1 cmd_ok ++ get_non_null c)
          * traced (expand_ktrace tr)
          * [exists i, s' = hdlr_state_run_cmd cc cm envd s c i]).
Proof.
  intros cc cm envd sinit cinit okinit;
  refine (Fix4
    (fun envd c s ok => tr :~~ ktr (hdlr_kst envd s) in
      hdlr_invariant cc cm s (projT1 ok)
      * traced (expand_ktrace tr))
    (fun envd c s ok (s' : hdlr_state envd) => tr :~~ ktr (hdlr_kst envd s') in
      hdlr_invariant cc cm s' (projT1 ok ++ get_non_null c)
      * traced (expand_ktrace tr)
      * [exists i, s' = hdlr_state_run_cmd cc cm envd s c i]
    )
    (fun self envd0 c s0 ok => _) envd cinit sinit okinit
  ).
  clear cinit sinit okinit envd HANDLERS IPROG IENVD.

  refine (
  (* /!\ We lose track of the let-open equalities if existentials remain,
         make sure that Coq can infer _all_ the underscores. *)
  match c as _c in cmd _ _envd return
    forall (s : hdlr_state _envd)
      (_ok : sigT (fun non_null:list (fin (projT1 _envd)) =>
           hdlr_cmd_ok (comp_type cc) (tag cm) _c non_null)),
    STsep
     (tr :~~ ktr (hdlr_kst _ s) in
         hdlr_invariant cc cm s (projT1 _ok) * traced (expand_ktrace tr))
     (fun s' : hdlr_state _envd =>
      tr :~~ ktr (hdlr_kst _envd s') in
         hdlr_invariant cc cm s' (projT1 _ok ++ get_non_null _c)
         * traced (expand_ktrace tr)
         * [exists i, s' = hdlr_state_run_cmd cc cm _envd s _c i])
  with

  | Nop _ => fun s ok => {{ Return s }}

  | Seq _ c1 c2 => fun s ok =>
    let case := "Seq _ c1 c2"%string in _

  | Ite _ cond c1 c2 => fun s ok =>
    let case := "Ite _ cond c1 c2"%string in _

  | Send _ ct ce t me => fun s ok =>
    let case := "Send _ ct ce t me"%string in _

  | Call _ ce argse i EQ => fun s ok =>
    let case := "Call _ ce argse i EQ"%string in _

  | InvokeFD _ ce argse i EQ => fun s ok =>
    let case := "InvokeFD _ ce argse i EQ"%string in _

  | InvokeStr _ ce argse i EQ => fun s ok =>
    let case := "InvokeStr _ ce argse i EQ"%string in _

  | Spawn _ ct cfge i EQ => fun s ok =>
    let case := "Spawn _ ct cfg i EQ"%string in _

  | StUpd _ i ve => fun s ok =>
    let case := "StUpd _ i ve"%string in _

  | CompLkup _ cp c1 c2 => fun s ok =>
    let case := "CompLkup _ cp c1 c2"%string in _

  end s0 ok
  ); sep unfoldr simplr_base. (*sep''; try subst v; sep'; simpl in *.*)

(* Seq *)
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
refine (
  s1 <- self _ c1 s (existT _ nn H1);
  s2 <- self _ c2 s1 (existT _ (nn ++ get_non_null c1) H2)
    <@> [exists i, s1 = hdlr_state_run_cmd _ _ envd s c1 i];
  {{ Return s2 }}
); sep unfoldr simplr_base.

(* Ite *)
destruct s as [ ks env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
refine (
  if num_eq (eval_hdlr_expr _ _ (kst (hdlr_kst _ s)) (hdlr_env _ s) cond) FALSE
  then s' <- self _ c2 s (existT _ nn H2); {{ Return s' }}
  else s' <- self _ c1 s (existT _ nn H1); {{ Return s' }}
); sep unfoldr simplr_base.

(*Send*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as Hok.
destruct Hok as [Hok1 Hok2].
refine (
  let c := projT1 (eval_hdlr_expr cc cm st env ce) in
  let m := eval_hdlr_payload_expr cc cm st _ env _ me in
  let msg := (Build_msg t m) in
  send_msg (comp_fd c) msg (tr ~~~ expand_ktrace tr)
    <@> (tr ~~ let fds := trace_fds (expand_ktrace tr) in
      all_open_drop fds (comp_fd c)
      * [In cc cs]
      * [all_comp_fds_in cs fds]
      * [vdesc_fds_all_in (pay cm) fds]
      * [vcdesc_fds_all_in st fds]
      * [forall i, In i nn ->
           in_if_fd_cdesc env i fds]);;

  {{ Return {| hdlr_kst :=
               {| kcs := cs
                ; ktr := tr ~~~ KSend c msg :: tr
                ; kst := st
                |}
               ; hdlr_env := env
               |}
  }}
); sep unfoldr simplr_base.

(*Spawn*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
refine (
  let c_cmd := compd_cmd (COMPS ct) in
  let c_args := compd_args (COMPS ct) in
  c_fd <- exec c_cmd c_args (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s nn;

  let cfg := eval_hdlr_payload_expr cc cm st _ env _ cfge in
  let c := {| comp_type := ct; comp_fd := c_fd; comp_conf := cfg |} in
  let tr := tr ~~~ KExec c_cmd c_args c :: tr in
  {{ Return {| hdlr_kst := {| kcs := c :: cs
                            ; ktr := tr
                            ; kst := st
                            |}
             ; hdlr_env := shvec_replace_cast EQ env (existT _ c (Logic.eq_refl ct))
             |}
  }}
); sep unfoldr simplr_base.

(*Call*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
refine (
  f <- call (eval_hdlr_expr _ _ _ _ ce)
            (map (eval_hdlr_expr _ _ _ _) argse)
            (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s nn;
  {{ Return
    {| hdlr_kst :=
      {| kcs := cs
       ; ktr := tr ~~~ KCall (eval_hdlr_expr _ _ _ _ ce)
                             (map (eval_hdlr_expr _ _ _ _) argse) f :: tr
       ; kst := st
       |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}
  }}
); sep unfoldr simplr_base.

(*InvokeFD*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
refine (
  f <- invoke_fd (eval_hdlr_expr _ _ _ _ ce)
            (map (eval_hdlr_expr _ _ _ _) argse)
            (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s nn;
  {{ Return
    {| hdlr_kst :=
      {| kcs := cs
       ; ktr := tr ~~~ KInvokeFD (eval_hdlr_expr _ _ _ _ ce)
                             (map (eval_hdlr_expr _ _ _ _) argse) f :: tr
       ; kst := st
       |}
     ; hdlr_env := shvec_replace_cast EQ env f
     |}
  }}
); sep unfoldr simplr_base.

(*InvokeStr*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
refine (
  res <- invoke_str (eval_hdlr_expr _ _ _ _ ce)
            (map (eval_hdlr_expr _ _ _ _) argse)
            (tr ~~~ expand_ktrace tr)
    <@> hdlr_invariant cc cm s nn;
  {{ Return
    {| hdlr_kst :=
      {| kcs := cs
       ; ktr := tr ~~~ KInvokeStr (eval_hdlr_expr _ _ _ _ ce)
                             (map (eval_hdlr_expr _ _ _ _) argse) res :: tr
       ; kst := st
       |}
     ; hdlr_env := shvec_replace_cast EQ env res
     |}
  }}
); sep unfoldr simplr_base.

(*StUpd*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold hdlr_cmd_ok in ok0.
simpl in ok0.
refine (
  let v := eval_hdlr_expr cc cm st env ve in
  {{ Return {| hdlr_kst := {| kcs := cs
                            ; ktr := tr
                            ; kst := shvec_replace_ith _ _ st i v
                            |}
             ; hdlr_env := env
             |}
  }}
); sep unfoldr simplr_base.

(*CompLkup*)
destruct s as [ [cs tr st] env]_eqn.
destruct ok0 as [nn ok0].
unfold init_cmd_ok in ok0.
simpl in ok0.
pose proof (andb_prop _ _ ok0) as H.
destruct H as [H1 H2].
pose (ocdp := find_comp (eval_hdlr_comp_pat cc cm st envd env cp) cs).
destruct ocdp as [ cdp | ]_eqn.
(*Component found*)
refine (
  let c := projT1 cdp in
  let d := Comp (comp_pat_type _ _ cp) in
  let new_envd := (existT _ (S (projT1 envd)) (svec_shift d (projT2 envd))) in
  let s' := Build_hdlr_state new_envd {| kcs := cs
                                       ; ktr := tr
                                       ; kst := st
                                       |}
                     (@shvec_shift cdesc sdenote_cdesc (projT1 envd) d
                       (existT _ c (projT2 cdp)) (projT2 envd) env) in
  s'' <- self new_envd c1 s' (existT _ (max_fin (projT1 envd) :: map lift_fin nn) H1);
  {{ Return {| hdlr_kst := hdlr_kst _ s''
             ; hdlr_env := shvec_unshift cdesc sdenote_cdesc (projT1 envd) d (projT2 envd) (hdlr_env _ s'')
             |}
  }}
); sep unfoldr simplr_base.
apply max_fin_in_shift; auto.
apply H0. unfold c0; eapply find_comp_suc_hdlr with (c:=cdp); eauto.
eapply fds_all_in_shift; eauto.
pose proof (in_map_iff lift_fin nn i).
destruct H6. specialize (H6 H7). destruct H6. destruct H6.
rewrite <- H6. apply lift_fin_not_max.
eapply fds_all_in_unshift; eauto.
intros. apply H7. right.
autorewrite with list in *. auto with datatypes v62.

(*Component not found*)
refine (
  s' <- self envd c2 s (existT _ nn H2);
  {{ Return s' }}
); sep unfoldr simplr_base.
Qed.

Theorem all_open_unconcat : forall a b,
  all_open (a ++ b) ==> all_open a * all_open b.
Proof.
  induction a.
  simpl. sep'.
  simpl. sep'.
Qed.

Lemma trace_recv_msg_fds : forall f m,
  trace_fds (trace_recv_msg f m) =
    rev (vdesc_fds _ (pay m)).
Proof.
  Local Transparent RecvNum RecvStr.
  intros f m.
  destruct m as [t p].
  unfold trace_recv_msg. simpl. destruct (num_of_fin t).
  destruct (lkup_tag t) as [n pd]. simpl in *.
  induction n.
    destruct pd. intuition.

    destruct pd. unfold vdesc_fds. simpl in *.
    destruct d; simpl in *.
      destruct p. unfold trace_payload_recv, trace_payload in *.
      simpl in *. rewrite <- app_assoc. rewrite trace_fds_dist.
      specialize (IHn s s1). rewrite trace_fds_dist in IHn.
      destruct s0. simpl in *. intuition.

      destruct p. unfold trace_payload_recv, trace_payload in *.
      simpl in *. rewrite <- app_assoc. rewrite trace_fds_dist.
      specialize (IHn s s1). rewrite trace_fds_dist in IHn.
      simpl in *. intuition.

      destruct p. unfold trace_payload_recv, trace_payload in *.
      simpl in *. rewrite <- app_assoc. rewrite trace_fds_dist.
      specialize (IHn s s1). rewrite trace_fds_dist in IHn.
      simpl in *. rewrite app_nil_r in IHn. rewrite IHn. intuition.
Qed.

Lemma rev_app : forall A (l:list A) a,
  rev (a::l) = (rev l) ++ (a::nil).
Proof.
  auto.
Qed.

Lemma all_open_rev : forall l,
  all_open l ==> all_open (rev l).
Proof.
  induction l.
    auto.

    rewrite rev_app. rewrite <- all_open_concat.
    sep'.
Qed.

Lemma vcdesc_fds_sub_app : forall vd (v:s[[vd]]) fds' fds,
  vcdesc_fds_all_in v fds ->
  vcdesc_fds_all_in v (fds' ++ fds).
Proof.
  intros vd v fds' fds Hin.
  induction fds'.
    intuition.

    simpl. apply vcdesc_fds_sub. auto.
Qed.

Lemma vdesc_fds_sub_app : forall vd (v:s[[vd]]) fds' fds,
  vdesc_fds_all_in v fds ->
  vdesc_fds_all_in v (fds' ++ fds).
Proof.
  intros vd v fds' fds Hin.
  induction fds'.
    intuition.

    simpl. apply vdesc_fds_sub. auto.
Qed.

Lemma all_comp_fds_in_sub_app : forall cs fds' fds,
  all_comp_fds_in cs fds ->
  all_comp_fds_in cs (fds' ++ fds).
Proof.
  intros cs fds' fds Hall_in.
  induction fds'.
    intuition.

    simpl. apply all_comp_fds_in_sub. auto.
Qed.

Definition sublist (l l':list fd) := forall f, In f l -> In f l'.

Lemma vdesc_fds_all_in_equiv : forall vd (v:s[[vd]]) l l',
  vdesc_fds_all_in v l ->
  sublist l l' ->
  vdesc_fds_all_in v l'.
Proof.
  intros vd v l l' Hall_in Hsub.
  intro i. specialize (Hall_in i).
  unfold in_if_fd_desc in *.
  destruct vd as [n vd].
  induction n.
    contradiction.

    simpl in *. destruct vd.
    destruct i; destruct d; simpl in *; auto.
      apply IHn; auto.
      apply IHn; auto.
      apply IHn; auto.
Qed.

Lemma sublist_app_l : forall l l',
  sublist l (l ++ l').
Proof.
  intros l l'.
  induction l.
    unfold sublist. intuition.

    unfold sublist. intros f Hin.
    destruct Hin. simpl. auto.
      simpl. right. auto.
Qed.

Lemma sublist_rev : forall l,
  sublist l (rev l).
Proof.
  unfold sublist.
  apply in_rev.
Qed.

Lemma vdesc_fds_all_in_refl : forall vd (v:s[[vd]]),
  vdesc_fds_all_in v (vdesc_fds _ v).
Proof.
  intros vd v.
  unfold vcdesc_fds_all_in.
  intro i. destruct vd as [n vd].
  induction n. 
    contradiction.

    destruct vd; destruct i; simpl in *;
    destruct d; simpl in *; destruct v; auto;
      unfold in_if_fd_desc, vdesc_fds in *; simpl in *;
      try apply IHn. apply in_if_fd_desc_right. apply IHn.
      left. auto.
Qed.

Ltac comp_in_cs_tac :=
  match goal with
  | [ Hin : In ?c ?cs,
      Hall_in : all_comp_fds_in ?cs ?fds_in |-
        In (comp_fd ?c) ?fds_in ]
    => specialize (Hall_in c Hin); auto
  end.

Ltac subst_states' :=
  repeat match goal with
         | [ s : init_state _ |- _ ]
           => subst s
         | [ s : hdlr_state _ |- _ ]
           => subst s
         | [ s : kstate |- _ ]
           => subst s
         end; simpl in *.

Ltac destruct_btag :=
  match goal with
  |- context[ btag ?m ]
    => destruct (btag m)
  end.

Ltac unfoldr_body :=
  unfoldr; unfold trace_recv_bogus_msg.

Ltac simplr_body :=
  subst_states';
  try uninhabit;
  discharge_pure;
  try apply unpack_all_open;
  try comp_in_cs_tac(*;
  try rewrite trace_fds_dist;
  try rewrite trace_recv_msg_fds;
  try rewrite <- app_assoc;
  try rewrite <- all_open_concat;
  try rewrite <- all_open_rev;
  try apply repack_all_open;
  try solve [eapply all_comp_fds_in_sub_app; eauto];
  try solve [eapply vcdesc_fds_sub_app; eauto];
  try solve [apply default_cpayload_fds]*).

Definition kbody:
  forall s,
  STsep (kstate_inv s)
        (fun s' => kstate_inv s').
Proof.
  intro s; destruct s as [cs tr st]_eqn; refine (
    let tr' := tr in
    c <- select_comp cs
    (tr ~~~ expand_ktrace tr)
    <@> (tr' ~~ let fds_tr := trace_fds (expand_ktrace tr') in
      all_open fds_tr * [Reach s] * [all_comp_fds_in cs fds_tr]
      * [vcdesc_fds_all_in st fds_tr]);

    let tr := tr ~~~ KSelect cs c :: tr in
    mm <- recv_msg (comp_fd c)
    (tr ~~~ expand_ktrace tr)
    <@> (tr' ~~ let fds_tr := trace_fds (expand_ktrace tr') in
      all_open_drop fds_tr (comp_fd c) * [In (comp_fd c) fds_tr] * [Reach s]
    * [all_comp_fds_in cs fds_tr] * [In c cs] * [vcdesc_fds_all_in st fds_tr]);

    match mm with
    | inl m =>
      let tr := tr ~~~ KRecv c m :: tr in
      let hdlrs := HANDLERS (tag m) (comp_type c) in
      let henv  := projT1 hdlrs in
      let hprog := projT2 hdlrs in
      let s' := {| hdlr_kst := {| kcs := cs
                                ; ktr := tr
                                ; kst := st
                                |}
                 ; hdlr_env := default_cpayload henv
                 |}
      in
      s'' <- run_hdlr_cmd c m henv s'
        (proj1_sig hprog) (existT _ nil (proj2_sig hprog))
      <@> [Reach s] * [In c cs];
      {{ Return (hdlr_kst _ s'') }}
    | inr m =>
      let tr := tr ~~~ KBogus c m :: tr in
      {{ Return {|kcs := cs; ktr := tr; kst := st |} }}
    end

  ); sep unfoldr_body simplr_body.

  unfold comp_fds_in in *. sep'.
  unfold comp_fds_in in *. sep'.

  rewrite trace_fds_dist. rewrite trace_recv_msg_fds.
  rewrite <- all_open_concat. rewrite <- all_open_rev.
  sep'. simpl. rewrite hstar_comm. apply repack_all_open. sep'.

  rewrite trace_fds_dist. eapply all_comp_fds_in_sub_app; eauto.

  rewrite trace_fds_dist. eapply vcdesc_fds_sub_app; eauto.

  rewrite trace_fds_dist. rewrite trace_recv_msg_fds.
  apply vdesc_fds_all_in_equiv with (l:=rev (vdesc_fds (lkup_tag (tag m)) (pay m))).
  apply vdesc_fds_all_in_equiv with (l:=vdesc_fds (lkup_tag (tag m)) (pay m)).
  apply vdesc_fds_all_in_refl.
  apply sublist_rev.
  apply sublist_app_l.

  match goal with
  | [ H : exists i : _, _ = _ |- _ ]
    => let i := fresh "i" in
       let Hin := fresh "Hin" in
       destruct H as [i Hin];
       eapply Reach_valid with (input:=i); eauto
       (*apply Reach_valid with (s:=s) (c:=c) (m:=m)
         (input:=i);
       auto*)
  end.
  subst_states'.
  econstructor; sep'; sep'.

  unfold trace_recv_bogus_msg.
  destruct_btag.
  apply repack_all_open; sep'.

  unfold trace_recv_bogus_msg.
  destruct_btag. sep'.

  unfold trace_recv_bogus_msg.
  destruct_btag. sep'.

  eapply Reach_bogus; eauto.
  econstructor; sep'.
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
