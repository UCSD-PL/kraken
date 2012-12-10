Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

(* follow ascii design, little endian *)
Inductive Num : Set :=
| num : ascii -> ascii -> Num.

Definition nat_of_Num (n : Num) : nat :=
  match n with
  | num l h => nat_of_ascii l + nat_of_ascii h * 256
  end.

Definition Num_of_nat (n : nat) : Num :=
  let l := n mod 256 in
  let h := n / 256 in
  num (ascii_of_nat l) (ascii_of_nat h).

Lemma nat_of_ascii_bound :
  forall x, nat_of_ascii x < 256.
Proof.
  destruct x.
  repeat (
    match goal with [ b : bool |- _ ] => destruct b end
  ); compute; omega.
Qed.

Lemma Num_nat_embedding :
  forall (n : Num), Num_of_nat (nat_of_Num n) = n.
Proof with try discriminate.
  destruct n as [[l h]]; simpl.
  unfold Num_of_nat, nat_of_Num.
  repeat f_equal.
  rewrite mod_add... rewrite mod_small. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
  rewrite div_add... rewrite div_small. simpl. now rewrite ascii_nat_embedding.
  apply nat_of_ascii_bound.
Qed.

Definition Num_eq (n1 n2 : Num) : {n1 = n2} + {n1 <> n2}.
  decide equality; apply ascii_dec.
Qed.

Definition Str : Set :=
  list ascii.

Fixpoint str_of_string (s : string) : Str :=
  match s with
  | EmptyString => nil
  | String c rest => c :: str_of_string rest
  end.

Definition FD : Set :=
  Num.

Definition FD_eq (f1 f2 : FD) : {f1 = f2} + {f1 <> f2} :=
  Num_eq f1 f2.

Lemma FD_eq_true :
  forall (f : FD) (A : Type) (vT vF : A),
  (if FD_eq f f then vT else vF) = vT.
Proof.
  intros; case (FD_eq f f); auto. congruence.
Qed.

Lemma FD_eq_false :
  forall (f1 f2 : FD) (A : Type) (vT vF : A),
  f1 <> f2 ->
  (if FD_eq f1 f2 then vT else vF) = vF.
Proof.
  intros; case (FD_eq f1 f2); auto. congruence.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_Num Num_of_nat.
