Require Import Ascii.
Require Import Eqdep_dec.
Require Import List.
Require Import NPeano.
Require Import String.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexHVec.
Require Import ReflexVec.

Ltac sep' := sep fail idtac.

Inductive Action : Set :=
| Exec   : str -> list str -> fd -> Action
| Call   : str -> list str -> fd -> Action
| Select : list fd -> fd -> Action
| Recv   : fd -> str -> Action
| Send   : fd -> str -> Action
| RecvFD : fd -> fd -> Action (* RecvFD f f' : use f to recv f' *)
| SendFD : fd -> fd -> Action (* SendFD f f' : use f to send f' *)
.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Axiom open : fd -> hprop.

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

Definition action_fds (a : Action) : FdSet.t :=
  match a with
  | Exec _ _ f => FdSet.singleton f
  | Call _ _ f => FdSet.singleton f
  | Select _ _ => FdSet.empty
  | Recv _ _   => FdSet.empty
  | Send _ _   => FdSet.empty
  | RecvFD _ f => FdSet.singleton f
  | SendFD _ _ => FdSet.empty
  end.

Definition trace_fds (tr : Trace) : FdSet.t :=
  fold_right (fun a b => FdSet.union (action_fds a) b) FdSet.empty tr.

(*
Axiom oracle : forall (d : desc) (tr : [Trace]), s[[ d ]].
*)

Axiom exec :
  forall (prog : str) (args : list str) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun f : fd => (tr ~~ open f * [~FdSet.In f (trace_fds tr)] *
            traced (Exec prog args f :: tr))).
(*
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

Record bogus_msg : Set :=
  { btag : num
  ; bbad : nat_of_num btag >= NB_MSG
  }.

Definition maybe_msg := (msg + bogus_msg)%type.

Inductive KAction : Set :=
| KExec   : str -> list str -> fd -> KAction
| KCall   : str -> list str -> fd -> KAction
| KSelect : list comp -> comp -> KAction
| KSend   : comp -> msg -> KAction
| KRecv   : comp -> msg -> KAction
| KBogus  : comp -> bogus_msg -> KAction
.

Definition KTrace : Set :=
  list KAction.

Definition proj_fds : list comp -> list fd :=
  map (fun comp => comp_fd comp).

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

Definition expand_kaction (ka : KAction) : Trace :=
  match ka with
  | KExec cmd args f => Exec cmd args f :: nil
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
*)

Axiom call :
  forall (prog : str) (args : list str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : fd => tr ~~ open f * [~FdSet.In f (trace_fds tr)] *
          traced (Call prog args f :: tr)).

Fixpoint in_fd (f : fd) (l : list fd) {struct l} : Set :=
  match l with
  | nil => False
  | x :: r => if fd_eq x f then True else in_fd f r
  end.

(* TODO add non-empty precondition *)
(* TODO add open w/ recv perms precondition *)
Axiom select :
  forall (fs : list fd) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun r : sigT (fun f : fd => in_fd f fs) =>
           tr ~~ traced (Select fs (projT1 r) :: tr) * [In (projT1 r) fs]).

Axiom recv :
  forall (f : fd) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun s : str => tr ~~ traced (Recv f s :: tr) * open f *
          [nat_of_num n = List.length s]).

Axiom send :
  forall (f : fd) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (Send f s :: tr) * open f).

Axiom recv_fd :
  forall (f : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun f' : fd => tr ~~ traced (RecvFD f f' :: tr) * open f * open f' *
          [~FdSet.In f' (trace_fds tr)]).

Axiom send_fd :
  forall (f : fd) (f' : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (SendFD f f' :: tr) * open f).

(* we use big endian to follow network order *)
Definition RecvNum (f : fd) (n : num) : Trace :=
  match n with
  | Num l h => Recv f (h :: l :: nil) :: nil
  end.

Definition SendNum (f : fd) (n : num) : Trace :=
  match n with
  | Num l h => Send f (h :: l :: nil) :: nil
  end.

Definition RecvStr (f : fd) (s : str) : Trace :=
  Recv f s :: RecvNum f (num_of_nat (List.length s)).

Definition SendStr (f : fd) (s : str) : Trace :=
  Send f s :: SendNum f (num_of_nat (List.length s)).

Definition recv_num:
  forall (f : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun n : num => tr ~~ traced (RecvNum f n ++ tr) * open f).
Proof.
  intros; refine (
    s <- recv f (Num "002" "000") tr;
    match s with
    | h :: l :: nil =>
      {{ Return (Num l h) }}
    | _ => (* bogus *)
      {{ Return (Num "000" "000") }}
    end
  );
  sep'; discriminate.
Qed.

Definition send_num:
  forall (f : fd) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (SendNum f n ++ tr) * open f).
Proof.
  intros; refine (
    match n with
    | Num l h =>
      send f (h :: l :: nil) tr;;
      {{ Return tt }}
    end
  );
  sep'.
Qed.

Definition recv_str:
  forall (f : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun s : str => tr ~~ traced (RecvStr f s ++ tr) * open f).
Proof.
  intros; refine (
    n <- recv_num f tr;
    s <- recv f n (tr ~~~ RecvNum f n ++ tr);
    {{ Return s }}
  );
  sep'.
  rewrite <- H.
  rewrite num_nat_embedding.
  sep'.
Qed.

Definition send_str:
  forall (f : fd) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun (_ : unit) => tr ~~ traced (SendStr f s ++ tr) * open f).
Proof.
  intros; refine (
    let n := num_of_nat (List.length s) in
    send_num f n tr;;
    send f s (tr ~~~ SendNum f n ++ tr);;
    {{ Return tt }}
  );
  sep'.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvNum SendNum RecvStr SendStr.

Fixpoint all_open (fds : list fd) : hprop :=
  match fds with
  | nil => emp
  | f :: fs => open f * all_open fs
  end.

Fixpoint all_open_drop (fds : list fd) (drop : fd) : hprop :=
  match fds with
  | nil => emp
  | f :: fs =>
    if fd_eq f drop
      then all_open fs
      else open f * all_open_drop fs drop
  end.

Lemma unpack_all_open :
  forall fs f,
  In f fs ->
  all_open fs ==> open f * all_open_drop fs f.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite fd_eq_true. apply himp_refl.
  case (fd_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_open :
  forall fs f,
  In f fs ->
  open f * all_open_drop fs f ==> all_open fs.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite fd_eq_true. apply himp_refl.
  case (fd_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.
