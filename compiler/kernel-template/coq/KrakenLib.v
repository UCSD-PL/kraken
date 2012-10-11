Require Import Ascii.
Require Import List.
Require Import String.

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

Fixpoint string2str (s: string): str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: string2str rest
  end.