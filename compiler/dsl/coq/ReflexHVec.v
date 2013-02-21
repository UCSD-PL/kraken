Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.

Section SHeterogeneousVector.

Variable desc : Set.
Variable sdenote_desc : desc -> Set.

Instance SDenoted_desc : SDenoted desc :=
{ sdenote := sdenote_desc
}.

Fixpoint shvec (n : nat) : svec desc n -> Set :=
  match n with
  | O => fun _ => unit
  | S n' => fun v =>
    match v with
    | (t, v') => s[[ t ]] * shvec n' v'
    end
  end%type.

Fixpoint shvec_ith (n : nat) :
  forall (v_d : svec desc n), shvec n v_d -> forall (i : fin n), s[[ svec_ith v_d i ]] :=
  match n with
  | O => fun _ _ i => match i with end
  | S n' => fun v_d =>
    match v_d with
    | (t, v_d') => fun v i =>
      match i with
      | None => fst v
      | Some i' => shvec_ith n' v_d' (snd v) i'
      end
    end
  end.

Axiom TODO : forall {T}, T.

Variable desc_eqdec : forall (x y : desc), decide (x = y).
Variable d : desc.
Variable x : s[[ d ]].

Fixpoint shvec_in (n : nat) :
  forall (vd : svec desc n), shvec n vd -> Prop :=
  match n with
  | O => fun _ _ => False
  | S n' => fun vd =>
    match vd as _vd return shvec (S n') _vd -> Prop with
    | (dd, vd') => fun vv =>
      let (v, vv') := vv in
      match desc_eqdec d dd with
      | left EQ =>
        (* need to cast v from s[[ dd ]] into s[[ d ]] to write eq *)
        match EQ in eq _ _dd return s[[ _dd ]] -> Prop with
        | eq_refl => fun v => v = x \/ shvec_in n' vd' vv'
        end v
      | right N => shvec_in n' vd' vv'
      end
    end
  end.

Variable repr_eqdec : forall (d : desc) (x y : s[[ d ]]), decide (x = y).

Fixpoint shvec_in_dec (n : nat) :
  forall (vd : svec desc n) (vv : shvec n vd), decide (shvec_in _ vd vv).
Proof.
  destruct n.
  simpl. refine (fun _ _ => right _ _). exact (fun x => match x with end).
  simpl.
  intros vd. destruct vd as [dd vd'].
  intros vv. destruct vv as [v vv'].
  destruct (desc_eqdec d dd).
  destruct e.
  destruct (repr_eqdec _ v x). left; tauto.
  destruct (shvec_in_dec _ _ vv'). left; tauto.
  right; tauto.
  exact (shvec_in_dec _ _ vv').
Qed.

End SHeterogeneousVector.

Implicit Arguments shvec [desc n].

Implicit Arguments shvec_ith [desc n].

Implicit Arguments shvec_in [desc n].

Theorem shvec_ith_in
  (desc : Set) (sdenote_desc : desc -> Set) desc_eqdec
  (UIP_refl_desc : forall (d : desc) (e : d = d), e = Logic.eq_refl d) (n : nat) :
  forall (vd : svec desc n) v i,
  shvec_in sdenote_desc desc_eqdec _ (shvec_ith _ vd v i) vd v.
Proof.
  intros. induction n. contradiction.
  simpl in vd. destruct vd as [d vd].
  simpl in v. destruct v as [x v].
  simpl in i. destruct i as [i|].
  simpl. destruct (desc_eqdec (svec_ith vd i) d).
  subst. right. apply IHn.
  apply IHn.
  simpl. destruct (desc_eqdec d d).
  rewrite (UIP_refl_desc _ e). now left.
  congruence.
Qed.

Implicit Arguments shvec_ith_in [desc n].

Section HeterogeneousVector.

Variable desc : Type.
Variable denote_desc : desc -> Type.

Instance Denoted_desc : Denoted desc :=
{ denote := denote_desc
}.

Fixpoint hvec (n : nat) : vec desc n -> Type :=
  match n with
  | O => fun _ => unit
  | S n' => fun v =>
    match v with
    | (t, v') => [[ t ]] * hvec n' v'
    end
  end%type.

Fixpoint hvec_ith (n : nat) :
  forall (v_d : vec desc n), hvec n v_d -> forall (i : fin n), [[ vec_ith v_d i ]] :=
  match n with
  | O => fun _ _ i => match i with end
  | S n' => fun v_d =>
    match v_d with
    | (t, v_d') => fun v i =>
      match i with
      | None => fst v
      | Some i' => hvec_ith n' v_d' (snd v) i'
      end
    end
  end.

End HeterogeneousVector.

Implicit Arguments hvec [desc n].

Implicit Arguments hvec_ith [desc n].
