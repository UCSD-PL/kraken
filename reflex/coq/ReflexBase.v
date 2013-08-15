Require Import Ascii.
Require Import Int.
Require Import List.
Require Import NPeano.
Require Import Omega.
Require Import Orders.
Require Import String.
Require Import Arith.Compare.

Notation decide P := ({ P } + { ~ P }).

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

Fixpoint pow (r: nat) (n: nat) : nat :=
  match n with
  | O => 1
  | S n => r * (pow r n)
  end.
Notation "r ^ n" := (pow r n).

Lemma N_of_digits_len : forall l, Nnat.nat_of_N (N_of_digits l) < (2 ^ (List.length l)).
Proof.
  unfold Nnat.nat_of_N.
  induction l.
  simpl;  omega.
  destruct a; simpl.
  destruct (N_of_digits l).
  unfold nat_of_P. simpl. omega.
  rewrite nat_of_P_xI. omega.
  destruct (N_of_digits l).
  omega.
  rewrite nat_of_P_xO. omega.
Qed.

Lemma nat_of_ascii_bound :
  forall x, nat_of_ascii x < 256.
Proof.
  unfold nat_of_ascii, Nnat.nat_of_N, N_of_ascii.
  repeat destruct x as [? x].
  match goal with |- match N_of_digits ?l with 0%N => _ | Npos p => _ end < _ =>
    pose proof (N_of_digits_len l) as P; destruct (N_of_digits l)
  end.
  omega.
  exact P.
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

Definition num_eq (n1 n2 : num) : decide (n1 = n2).
  decide equality; apply ascii_dec.
Defined.

Notation FALSE := (Num "000" "000").
Notation TRUE  := (Num "001" "000").

Definition str : Set :=
  list ascii.

Fixpoint str_of_string (s : string) : str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: str_of_string rest
  end.

Definition str_eq (s1 s2 : str) : decide (s1 = s2) :=
  list_eq_dec ascii_dec s1 s2.

Definition fd : Set :=
  num.

Definition fd_eq (f1 f2 : fd) : decide (f1 = f2) :=
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