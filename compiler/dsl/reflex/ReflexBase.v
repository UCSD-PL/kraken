Require Import List.
Require Import Ascii.
Require Import String.
Require Import NPeano.
Require Import Ynot.

Open Scope char_scope.
Open Scope hprop_scope.
Open Scope stsepi_scope.

Ltac sep' := sep fail idtac.
Ltac inv H := inversion H; subst; clear H.

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

(* prevent sep tactic from unfolding *)
Global Opaque nat_of_Num Num_of_nat Num_eq.

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

Inductive Action : Set :=
| Exec   : Str -> FD -> Action
| Call   : Str -> Str -> FD -> Action
| Select : list FD -> FD -> Action
| Recv   : FD -> Str -> Action
| Send   : FD -> Str -> Action
| RecvFD : FD -> FD -> Action (* RecvFD f f' : use f to recv f' *)
| SendFD : FD -> FD -> Action (* SendFD f f' : use f to send f' *)
.

Definition Trace : Set := list Action.

Axiom traced : Trace -> hprop.

Inductive Perm : Set :=
  RecvP | SendP | RecvFDP | SendFDP.

Definition ExecPerms : list Perm :=
  RecvP :: SendP :: RecvFDP :: SendFDP :: nil.

Definition CallPerms : list Perm :=
  RecvP :: RecvFDP :: nil.

Axiom open : FD -> list Perm -> hprop.

Axiom exec :
  forall (prog : Str) (tr : [Trace]),
    STsep (tr ~~ traced tr)
          (fun f : FD => tr ~~ open f ExecPerms * traced (Exec prog f :: tr)).

Axiom call :
  forall (prog arg : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : FD => tr ~~ open f CallPerms * traced (Call prog arg f :: tr)).

(* TODO add non-empty precondition *)
(* TODO add open w/ recv perms precondition *)
Axiom select :
  forall (fs : list FD) (tr : [Trace]),
  STsep (tr ~~ traced tr)
        (fun f : FD => tr ~~ traced (Select fs f :: tr) * [In f fs]).

Axiom recv :
  forall (f : FD) (ps : list Perm) (n : Num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun s : Str => tr ~~ traced (Recv f s :: tr) * open f ps *
          [nat_of_Num n = List.length s]).

Axiom send :
  forall (f : FD) (ps : list Perm) (s : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun _ : unit => tr ~~ traced (Send f s :: tr) * open f ps).

Axiom recv_fd :
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvFDP ps])
        (fun f' : FD => tr ~~ traced (RecvFD f f' :: tr) * open f ps).

Axiom send_fd :
  forall (f : FD) (ps : list Perm) (f' : FD) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendFDP ps])
        (fun _ : unit => tr ~~ traced (SendFD f f' :: tr) * open f ps).

(* we use big endian to follow network order *)
Definition RecvNum (f : FD) (n : Num) : Trace :=
  match n with
  | num l h => Recv f (h :: l :: nil) :: nil
  end.

Definition SendNum (f : FD) (n : Num) : Trace :=
  match n with
  | num l h => Send f (h :: l :: nil) :: nil
  end.

Definition RecvStr (f : FD) (s : Str) : Trace :=
  Recv f s :: RecvNum f (Num_of_nat (List.length s)).

Definition SendStr (f : FD) (s : Str) : Trace :=
  Send f s :: SendNum f (Num_of_nat (List.length s)).

Definition recv_num:
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun n : Num => tr ~~ traced (RecvNum f n ++ tr) * open f ps).
Proof.
  intros; refine (
    s <- recv f ps (num "002" "000") tr;
    match s with
    | h :: l :: nil =>
      {{ Return (num l h) }}
    | _ => (* bogus *)
      {{ Return (num "000" "000") }}
    end
  );
  sep'; discriminate.
Qed.

Definition send_num:
  forall (f : FD) (ps : list Perm) (n : Num) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun _ : unit => tr ~~ traced (SendNum f n ++ tr) * open f ps).
Proof.
  intros; refine (
    match n with
    | num l h =>
      send f ps (h :: l :: nil) tr;;
      {{ Return tt }}
    end
  );
  sep'.
Qed.

Definition recv_str:
  forall (f : FD) (ps : list Perm) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In RecvP ps])
        (fun s : Str => tr ~~ traced (RecvStr f s ++ tr) * open f ps).
Proof.
  intros; refine (
    n <- recv_num f ps tr <@> [In RecvP ps];
    s <- recv f ps n (tr ~~~ RecvNum f n ++ tr);
    {{ Return s }}
  );
  sep'.
  rewrite <- H.
  rewrite Num_nat_embedding.
  sep'.
Qed.

Definition send_str:
  forall (f : FD) (ps : list Perm) (s : Str) (tr : [Trace]),
  STsep (tr ~~ traced tr * open f ps * [In SendP ps])
        (fun (_ : unit) => tr ~~ traced (SendStr f s ++ tr) * open f ps).
Proof.
  intros; refine (
    let n := Num_of_nat (List.length s) in
    send_num f ps n tr <@> [In SendP ps];;
    send f ps s (tr ~~~ SendNum f n ++ tr);;
    {{ Return tt }}
  );
  sep'.
Qed.

(* prevent sep tactic from unfolding *)
Global Opaque RecvNum SendNum RecvStr SendStr.

Definition bound (f : FD) : hprop :=
  open f ExecPerms.

Fixpoint all_bound (fds : list FD) : hprop :=
  match fds with
  | nil => emp
  | f :: fs => bound f * all_bound fs
  end.

Fixpoint all_bound_drop (fds : list FD) (drop : FD) : hprop :=
  match fds with
  | nil => emp
  | f :: fs =>
    if FD_eq f drop
      then all_bound fs
      else bound f * all_bound_drop fs drop
  end.

Lemma unpack_all_bound :
  forall fs f,
  In f fs ->
  all_bound fs ==> bound f * all_bound_drop fs f.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite FD_eq_true. apply himp_refl.
  case (FD_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_conc. apply himp_assoc_conc1.
  apply himp_split. apply himp_refl.
  apply himp_comm_conc; auto.
Qed.

Lemma repack_all_bound :
  forall fs f,
  In f fs ->
  bound f * all_bound_drop fs f ==> all_bound fs.
Proof.
  induction fs; simpl; intros. contradiction.
  destruct H; subst. rewrite FD_eq_true. apply himp_refl.
  case (FD_eq a f); intros; subst. apply himp_refl.
  apply himp_comm_prem. apply himp_assoc_prem1.
  apply himp_split. apply himp_refl.
  apply himp_comm_prem; auto.
Qed.