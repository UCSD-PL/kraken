Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

Require Import ReflexBase.

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

Axiom exec :
  forall (prog : str) (args : list str) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun f : fd => tr ~~ open f * traced (Exec prog args f :: tr)).

Axiom call :
  forall (prog : str) (args : list str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : fd => tr ~~ open f * traced (Call prog args f :: tr)).

(* TODO add non-empty precondition *)
(* TODO add open w/ recv perms precondition *)
Axiom select :
  forall (fs : list fd) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : fd => tr ~~ traced (Select fs f :: tr) * [In f fs]).

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
        (fun f' : fd => tr ~~ traced (RecvFD f f' :: tr) * open f * open f').

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