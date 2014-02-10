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

(* Contains primitives for interacting with the outside
world. Their behavior (in terms of observable actions produced and
facts about open file descriptors) is specified by axioms. Contains a
few lemmas for reasoning about open file descriptors.*)

Ltac sep' := sep fail idtac.

(* Defines the observable interactions with the outside world.*)
Inductive Action : Set :=
| Exec   : str -> list str -> fd -> Action
| Call   : str -> list str -> fd -> Action
| Select : list fd -> fd -> Action
| Recv   : fd -> str -> Action
| Send   : fd -> str -> Action
| RecvFD : fd -> fd -> Action (* RecvFD f f' : use f to recv f' *)
| SendFD : fd -> fd -> Action (* SendFD f f' : use f to send f' *)
.

(* Represents the sequence of observable interactions with the outside
world.*)
Definition Trace : Set := list Action.

(* Used to ensure that traces are unforgeable.*)
Axiom traced : Trace -> hprop.

(* Represents that a file descriptor is open.*)
Axiom open : fd -> hprop.

(* Type descriptors for num, str, and fd.*)
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

(* Denotations of each of the type descriptors.*)
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

(* Projects any newly opened file descriptors from an action.*)
Definition action_fds (a : Action) : list fd :=
  match a with
  | Exec _ _ f => f::nil
  | Call _ _ f => f::nil
  | Select _ _ => nil
  | Recv _ _   => nil
  | Send _ _   => nil
  | RecvFD _ f => f::nil
  | SendFD _ _ => nil
  end.

(* Projects all open file descriptors from a trace.*)
Definition trace_fds (tr : Trace) : list fd :=
  flat_map action_fds tr.

Definition devnull := Num "000" "000".

Axiom devnull_open : emp ==> open devnull.

(* Primitive for spawning a new component.*)
Axiom exec :
  forall (prog : str) (args : list str) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun f : fd => (tr ~~ open f *
            traced (Exec prog args f :: tr))).

(* Primitive for spawning a new process. Currently has the same type
as exec, but exec should be used for new components while call should
be used for spawning arbitrary new processes. Used as a way of
extending the set of primitives (e.g. could be used to add a wget
primitive)*)
Axiom call :
  forall (prog : str) (args : list str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : fd => tr ~~ open f *
          traced (Call prog args f :: tr)).

Fixpoint in_fd (f : fd) (l : list fd) {struct l} : Set :=
  match l with
  | nil => False
  | x :: r => if fd_eq x f then True else in_fd f r
  end.

(* Primitive for performing Unix-style select on a list of fds.*)
(* TODO add non-empty precondition *)
(* TODO add open w/ recv perms precondition *)
Axiom select :
  forall (fs : list fd) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun r : sigT (fun f : fd => in_fd f fs) =>
           tr ~~ traced (Select fs (projT1 r) :: tr) * [In (projT1 r) fs]).

(* Primitive for reading a str from a fd.*)
Axiom recv :
  forall (f : fd) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun s : str => tr ~~ traced (Recv f s :: tr) * open f *
          [nat_of_num n = List.length s]).

(* Primitive for sending a str over an fd.*)
Axiom send :
  forall (f : fd) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (Send f s :: tr) * open f).

(* Primitive for reading an fd from an fd.*)
Axiom recv_fd :
  forall (f : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun f' : fd => tr ~~ traced (RecvFD f f' :: tr) * open f * open f').

(* Primitive for sending an fd over an fd.*)
Axiom send_fd :
  forall (f : fd) (f' : fd) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f)
        (fun _ : unit => tr ~~ traced (SendFD f f' :: tr) * open f).

(* Gives the trace appended when a num is read from an fd.*)
(* we use big endian to follow network order *)
Definition RecvNum (f : fd) (n : num) : Trace :=
  match n with
  | Num l h => Recv f (h :: l :: nil) :: nil
  end.

(* Gives the trace appended when a num is sent to an fd.*)
Definition SendNum (f : fd) (n : num) : Trace :=
  match n with
  | Num l h => Send f (h :: l :: nil) :: nil
  end.

(* Gives the trace appended when a str is received from an fd.*)
Definition RecvStr (f : fd) (s : str) : Trace :=
  Recv f s :: RecvNum f (num_of_nat (List.length s)).

(* Gives the trace appended when a str is sent to an fd.*)
Definition SendStr (f : fd) (s : str) : Trace :=
  Send f s :: SendNum f (num_of_nat (List.length s)).

(* Reads a num from an fd, building on recv primitive.*)
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

(* Sends a num to an fd, building on send primitive.*)
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

(* Reads a str from an fd, building on recv primitive.*)
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

(* Sends a str to an fd, building on recv primitive.*)
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

(* All fds in the input list are open.*)
Fixpoint all_open (fds : list fd) : hprop :=
  match fds with
  | nil => emp
  | f :: fs => open f * all_open fs
  end.

(* All fds except for the given fd are open.*)
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
