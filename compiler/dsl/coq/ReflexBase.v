Require Import Ascii.
Require Import Int.
Require Import List.
Require Import MSetAVL.
Require Import MSetInterface.
Require Import NPeano.
Require Import Omega.
Require Import Orders.
Require Import String.

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

Module OrderedFd : OrderedType
  with Definition t := fd
  with Definition eq := @eq fd
  .

  Definition t := fd.

  Definition eq := @eq fd.

  Parameter eq_equiv : Equivalence eq.

  Parameter lt : t -> t -> Prop.

  Parameter lt_strorder : StrictOrder lt.

  Parameter lt_compat : Morphisms.Proper (eq ==> eq ==> iff) lt.

  Parameter compare : t -> t -> comparison.

  Parameter compare_spec :
    forall x y : t, CompSpec eq lt x y (compare x y).

  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.

End OrderedFd.

Module RawFdSet : RawSets OrderedFd := MSetAVL.MakeRaw(Int.Z_as_Int)(OrderedFd).

Module FdSet : Sets
  with Module E := OrderedFd
  := Raw2Sets(OrderedFd)(RawFdSet)
.
