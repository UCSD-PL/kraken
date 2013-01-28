Require Import Arith.

Require Import ReflexBase.

(* isomorphic to nats less than n *)
Fixpoint fin (n : nat) : Set :=
  match n with
  | O => False
  | S n' => option (fin n')
  end.

Fixpoint nat_of_fin (bound : nat) (n : fin bound) :=
  match bound as _bound return fin _bound -> _ with
  | O => fun n => match n with end
  | S bound' => fun n =>
    match n with
    | None => O
    | Some n' => S (nat_of_fin bound' n')
    end
  end n.

Implicit Arguments nat_of_fin [bound].

Fixpoint opt_fin (bound : nat) (n : nat)
  : {f : fin bound & nat_of_fin f = n } + { n >= bound } :=
  let ret b n := { f : fin b & nat_of_fin f = n } + { n >= b } in
  match bound as _bound return ret _bound n with
  | O => inright _ (le_0_n _)
  | S bound' =>
    match n as _n return ret (S bound') _n with
    | O => inleft _ (existT _ None (eq_refl O))
    | S n' =>
      match opt_fin bound' n' with
      | inleft (existT f' eq') =>
        inleft _ (existT _ (Some f') (eq_ind_r (fun n => S n = S n') (eq_refl (S n')) eq'))
      | inright pf => inright _ (le_n_S _ _ pf)
      end
    end
  end.

(* same number, increment bound *)
Fixpoint lift_fin {n} (f : fin n) : fin (S n) :=
  match n as _n return fin _n -> fin (S _n) with
  | O => fun f => match f with end
  | S n' => fun f =>
    match f with
    | None => None
    | Some f' =>
      let lf' : fin (S n') := lift_fin f' in
      Some lf'
    end
  end f.

(* increment number and bound *)
Fixpoint shift_fin {n} (f : fin n) : fin (S n) :=
  match n as _n return fin _n -> fin (S _n) with
  | O => fun f => match f with end
  | S n' => fun f =>
    match f with
    | None => Some None
    | Some f' => Some (Some f')
    end
  end f.

(* returns [n] as a [fin (S n)] *)
Fixpoint max_fin n : fin (S n) :=
  match n as _n return fin (S _n) with
  | O => None
  | S n' => Some (max_fin n')
  end.

(* turns a [fin (S n)] into a [fin n] if possible, returns a proof that it cannot otherwise *)
Fixpoint proj_fin n (f : fin (S n)) : (fin n) + (f = max_fin n) :=
  let res n f := ((fin n) + (f = max_fin n))%type in
  match n as _n return
    forall (f : fin (S _n)), res _n f
  with
  | O => fun f =>
    match f as _f return res 0 _f with
    | None => inr _ (eq_refl None)
    | Some f' => match f' with end
    end
  | S n' => fun f =>
    match f as _f return res (S n') _f with
    | None => inl _ None
    | Some f' =>
      match proj_fin _ f' with
      | inl p => inl _ (Some p)
      | inr p => inr _ (eq_ind_r
                          (fun f => Some f = max_fin (S n'))
                          (eq_refl (max_fin (S n'))) p)
      end
    end
  end f.

Definition proj_fin_ok {n} (f : fin (S n)) (H : f <> max_fin n) : fin n :=
  match proj_fin n f with
  | inl f => f
  | inr P => match H P with end
  end.

Theorem nat_of_proj_fin_ok : forall n (f : fin (S n)) H,
  nat_of_fin (proj_fin_ok f H) = nat_of_fin f.
Proof.
  intros. induction n.
  simpl. destruct f. destruct f. simpl in H. now elim H.
  simpl in f. destruct f as [f|].
  specialize (IHn f (fun EQ => H (f_equal (@Some _) EQ))).
  simpl in *. unfold proj_fin_ok in *. destruct f.
  rewrite <- IHn. clear IHn. simpl. destruct (proj_fin n (Some f)) as []_eqn.
  reflexivity. elim H. now rewrite e.
  simpl. destruct (proj_fin n (@None (fin n))) as []_eqn. auto.
  destruct (H (f_equal _ e)).
  now simpl.
Qed.

Definition fin_eq_dec : forall {n} (x y : fin n), decide (x = y).
Proof.
  intros. induction n. destruct x.
  simpl in x, y. destruct x as [x|], y as [y|].
  destruct (IHn x y). left. now subst. right. congruence.
  now right. now right. now left.
Qed.

Definition proj_prop_fin {n} (P : fin (S n) -> Prop) : (fin n -> Prop) :=
  fun fn => P (lift_fin fn).

Theorem lift_proj_fin : forall n i OK, lift_fin (@proj_fin_ok n i OK) = i.
Proof.
  intros. induction n.
  destruct i. destruct f. simpl in OK. congruence.
  simpl in i. destruct i as [i|].
  specialize (IHn i (fun EQ => OK (f_equal (@Some _) EQ))).
  simpl. unfold proj_fin_ok in *. simpl.
  destruct (proj_fin n i) as []_eqn. now rewrite IHn.
  destruct (OK (f_equal _ e)).
  now simpl.
Qed.

Definition forall_fin {n : nat} {P : fin n -> Prop} (Pdec : forall i, decide (P i))
  : decide (forall i, P i).
Proof.
  induction n.
  left. destruct 0.
  specialize (IHn (proj_prop_fin P) (fun i => Pdec (lift_fin i))).
  unfold proj_prop_fin in IHn.
  destruct IHn. destruct (Pdec (max_fin n)).
  left.
  intros i.
  destruct (fin_eq_dec i (max_fin n)).
  now subst. specialize (p (proj_fin_ok i n0)).
  now rewrite lift_proj_fin in p.
  right. intro H. exact (n0 (H (max_fin n))).
  right. intro. apply n0. intro. apply H.
Qed.

Definition fin_ind : forall {n} {P},
  (forall i : fin n, proj_prop_fin P i) ->
  (P (max_fin n)) ->
  forall i : fin (S n), P i.
Proof.
  intros n P PP PM. destruct n. destruct i. destruct f. exact PM.
  intros i. destruct (fin_eq_dec i (max_fin (S n))).
  now subst.
  specialize (PP (proj_fin_ok i n0)).
  unfold proj_prop_fin in PP. now rewrite lift_proj_fin in PP.
Qed.
