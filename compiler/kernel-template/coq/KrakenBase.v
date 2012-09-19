Require Import List.
Require Import Ascii.
Require Import Ynot.

Open Local Scope char_scope.
Open Local Scope hprop_scope.
Open Local Scope stsepi_scope.

Definition str : Set := list ascii.

Inductive num : Set :=
| Num : ascii -> num.

Definition nat_of_num (n : num) : nat :=
  match n with
    | Num a1 => nat_of_ascii a1
  end.

Definition num_of_nat (n : nat) : num :=
  Num (ascii_of_nat n).

Lemma num_nat_embedding :
  forall (n : num), num_of_nat (nat_of_num n) = n.
Proof.
  destruct n; simpl.
  unfold num_of_nat, nat_of_num.
  rewrite ascii_nat_embedding; auto.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_num num_of_nat.

Axiom chan : Set.
Axiom fdesc : Set.

Inductive Action : Set :=
| Exec : str -> chan -> Action
| Call : str -> str -> fdesc -> Action
| Recv : chan -> str -> Action
| Send : chan -> str -> Action
| RecvFD : chan -> fdesc -> Action
| SendFD : chan -> fdesc -> Action.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.
Axiom bound : chan -> hprop.

Axiom exec :
  forall (prog : str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (c : chan) => tr ~~ traced (Exec prog c :: tr)).

Axiom call :
  forall (prog arg : str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (f : fdesc) => tr ~~ traced (Call prog arg f :: tr)).

Axiom recv :
  forall (c : chan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (Recv c s :: tr) * bound c * [nat_of_num n = length s]).

Axiom send :
  forall (c : chan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (Send c s :: tr) * bound c).

Axiom recv_fd :
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (f : fdesc) => tr ~~ traced (RecvFD c f :: tr) * bound c).

Axiom send_fd :
  forall (c : chan) (f : fdesc) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendFD c f :: tr) * bound c).

Definition RecvNum (c : chan) (n : num) : Trace :=
  match n with
    | Num a1 => Recv c (a1 :: nil) :: nil
  end.

Definition recv_num:
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (n : num) => tr ~~ traced (RecvNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    s <- recv c (Num "001") tr;
    match s with
      | a1 :: nil =>
        {{ Return (Num a1) }}
      | _ => (* bogus *)
        {{ Return (Num zero) }}
    end
  );
  sep fail auto.
  compute in H; discriminate.
  compute in H; discriminate.
Qed.

Definition SendNum (c : chan) (n : num) : Trace :=
  match n with
    | Num a1 => Send c (a1 :: nil) :: nil
  end.

Definition send_num:
  forall (c : chan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    match n with
      | Num a1 =>
        send c (a1 :: nil) tr;;
        {{ Return tt }}
    end
  );
  sep fail auto.
Qed.

Definition RecvStr (c : chan) (s : str) : Trace :=
  Recv c s :: RecvNum c (num_of_nat (length s)).

Definition recv_str:
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (RecvStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recv_num c tr;
    s <- recv c n (tr ~~~ RecvNum c n ++ tr);
    {{ Return s }}
  );
  sep fail auto.
  rewrite <- H.
  rewrite num_nat_embedding.
  sep fail auto.
Qed.

Definition SendStr (c : chan) (s : str) : Trace :=
  Send c s :: SendNum c (num_of_nat (length s)).

Definition send_str:
  forall (c : chan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    let n := num_of_nat (length s) in
    send_num c n tr;;
    send c s (tr ~~~ SendNum c n ++ tr);;
    {{ Return tt }}
  );
  sep fail auto.  
Qed.

(* trace versions of basic actions so we can always use app (++) *)

Definition Call_t (prog arg : str) (f : fdesc) : Trace :=
  Call prog arg f :: nil.

Definition RecvFD_t (c : chan) (f : fdesc) : Trace :=
  RecvFD c f :: nil.

Definition SendFD_t (c : chan) (f : fdesc) : Trace :=
  SendFD c f :: nil.

(* prevent sep tactic from unfolding *)
Global Opaque RecvStr SendStr Call_t RecvFD_t SendFD_t.
