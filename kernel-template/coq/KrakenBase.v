Require Import List.
Require Import Ascii.
Require Import Ynot.

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

(* prevent sep tactic from unfolding these *)
Opaque nat_of_num.
Opaque num_of_nat.

Definition num_0 : num := Num Ascii.zero.
Definition num_1 : num := Num Ascii.one.

Axiom chan : Set.

Inductive Action : Set :=
| Exec : str -> chan -> Action
| Recv : chan -> str -> Action
| Send : chan -> str -> Action.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.
Axiom bound : chan -> hprop.

Axiom exec :
  forall (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun (c : chan) => tr ~~ traced (Exec s c :: tr)).

Axiom recv :
  forall (c : chan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (Recv c s :: tr) * bound c * [nat_of_num n = length s]).

Axiom send :
  forall (c : chan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (Send c s :: tr) * bound c).

Definition RecvNum (c : chan) (n : num) : Trace :=
  match n with
    | Num a1 => Recv c (a1 :: nil) :: nil
  end.

Definition recvNum:
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (n : num) => tr ~~ traced (RecvNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    s <- recv c num_1
      tr;
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

Definition sendNum:
  forall (c : chan) (n : num) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendNum c n ++ tr) * bound c).
Proof.
  intros; refine (
    match n with
      | Num a1 =>
        send c (a1 :: nil)
          tr;;
        {{ Return tt }}
    end
  );
  sep fail auto.
Qed.

Definition RecvStr (c : chan) (s : str) : Trace :=
  Recv c s :: RecvNum c (num_of_nat (length s)).

Definition recvStr:
  forall (c : chan) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (s : str) => tr ~~ traced (RecvStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    n <- recvNum c
      tr;
    s <- recv c n
      (tr ~~~ RecvNum c n ++ tr);
    {{ Return s }}
  );
  sep fail auto.
  rewrite <- H.
  rewrite num_nat_embedding.
  sep fail auto.
Qed.

Definition SendStr (c : chan) (s : str) : Trace :=
  Send c s :: SendNum c (num_of_nat (length s)).

Definition sendStr:
  forall (c : chan) (s : str) (tr : [Trace]),
  STsep (tr ~~ traced tr * bound c)
        (fun (_ : unit) => tr ~~ traced (SendStr c s ++ tr) * bound c).
Proof.
  intros; refine (
    let n := num_of_nat (length s) in
    sendNum c n
      tr;;
    send c s
      (tr ~~~ SendNum c n ++ tr);;
    {{ Return tt }}
  );
  sep fail auto.  
Qed.
