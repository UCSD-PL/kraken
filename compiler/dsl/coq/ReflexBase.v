Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

(* follow ascii design, little endian *)
Inductive num : Set :=
| Num : ascii -> ascii -> num.

Definition nat_of_num (n : num) : nat :=
  match n with
  | Num l h => nat_of_ascii l + nat_of_ascii h * 256
  end.

Definition num_of_nat (n : nat) : num :=
  let l := n mod 256 in
  let h := n / 256 in
  Num (ascii_of_nat l) (ascii_of_nat h).

Lemma nat_of_ascii_bound :
  forall x, nat_of_ascii x < 256.
Proof.
  destruct x.
  repeat (
    match goal with [ b : bool |- _ ] => destruct b end
  ); compute; omega.
Qed.

Lemma num_nat_embedding :
  forall (n : num), num_of_nat (nat_of_num n) = n.
Proof with try discriminate.
  destruct n as [[l h]]; simpl.
  unfold num_of_nat, nat_of_num.
  repeat f_equal.
  rewrite mod_add... rewrite mod_small. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
  rewrite div_add... rewrite div_small. simpl. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
Qed.

Definition num_eq (n1 n2 : num) : {n1 = n2} + {n1 <> n2}.
  decide equality; apply ascii_dec.
Qed.

Definition str : Set :=
  list ascii.

Fixpoint str_of_string (s : string) : str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: str_of_string rest
  end.

Definition str_eq (s1 s2 : str) : {s1 = s2} + {s1 <> s2} :=
  list_eq_dec ascii_dec s1 s2.

Definition fd : Set :=
  num.

Definition fd_eq (f1 f2 : fd) : {f1 = f2} + {f1 <> f2} :=
  num_eq f1 f2.

Lemma fd_eq_true :
  forall (f : fd) (A : Type) (vT vF : A),
  (if fd_eq f f then vT else vF) = vT.
Proof.
  intros; case (fd_eq f f); auto. congruence.
Qed.

Lemma fd_eq_false :
  forall (f1 f2 : fd) (A : Type) (vT vF : A),
  f1 <> f2 ->
  (if fd_eq f1 f2 then vT else vF) = vF.
Proof.
  intros; case (fd_eq f1 f2); auto. congruence.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_num num_of_nat.
