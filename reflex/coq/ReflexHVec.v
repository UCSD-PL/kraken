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

Fixpoint shvec_shift (n : nat) (d : desc) (e : s[[d]]) :
  forall (v_d : svec desc n), shvec n v_d -> shvec (S n) (svec_shift d v_d) :=
  match n
  with
  | O => fun _ _ => (e, tt)
  | S n' => fun v_d =>
    match v_d with
    | (_, _) => fun v =>
      (fst v, shvec_shift n' d e _ (snd v))
    end
  end.

Fixpoint shvec_unshift (n : nat) (d : desc) :
  forall (v_d : svec desc n), shvec (S n) (svec_shift d v_d) -> shvec n v_d :=
  match n as _n return
    forall (v_d : svec desc _n), shvec (S _n) (svec_shift d v_d) -> shvec _n v_d
  with
  | O => fun _ _ => tt
  | S n' => fun v_d =>
    match v_d with
    | (_, _) => fun v =>
      (fst v, shvec_unshift n' d _ (snd v))
    end
  end.

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

Fixpoint shvec_replace_ith (n : nat) : forall (v_d : svec desc n),
  shvec n v_d -> forall (i : fin n), s[[ svec_ith v_d i ]] -> shvec n v_d :=
  match n with
  | O => fun _ _ i => match i with end
  | S n' => fun v_d =>
    match v_d with
    | (t, v_d') => fun v i =>
      match i with
      | None    => fun ith => (ith, snd v)
      | Some i' => fun ith => (fst v, shvec_replace_ith n' v_d' (snd v) i' ith)
      end
    end
  end.

Fixpoint shvec_eq (n:nat):
  forall (vd:svec desc n) (v1:shvec n vd) (v2:shvec n vd)
    (lblr:fin n -> bool), Prop :=
  match n as _n return
    forall (vd:svec desc _n) (v1:shvec _n vd) (v2:shvec _n vd)
      (lblr:fin _n -> bool), Prop
  with
  | O => fun _ _ _ _ => True
  | S n' => fun (vd:svec desc (S n')) =>
    match vd as _vd return
      forall (v1:shvec (S n') _vd) (v2:shvec (S n') _vd)
        (lblr:fin (S n') -> bool), Prop
    with
    | (h, vd') => fun v1 v2 lblr =>
      let lblr' := fun (f:fin n') => lblr (shift_fin f) in
      let rest_eq := shvec_eq n' vd' (snd v1) (snd v2) lblr' in
      if lblr None
      then if repr_eqdec h (fst v1) (fst v2)
           then rest_eq
           else False
      else rest_eq
    end
  end.

Lemma shvec_eq_sym : forall n vd v1 v2 lblr,
  shvec_eq n vd v1 v2 lblr <->
  shvec_eq n vd v2 v1 lblr.
Proof.
  intros.
  induction n.
    tauto.

    simpl in *.
    destruct vd as [h vd'].
    repeat match goal with
           | [ |- (if ?e1 then _ else _) <-> (if ?e2 then _ else _)]
             => destruct e1; destruct e2
           end; auto; try tauto;
           try match goal with
               | [ H : ?x = ?y, H' : ?y <> ?x |- _ ]
                 => symmetry in H; contradiction
               end.
Qed.

Lemma shvec_eq_refl : forall n vd v lblr,
  shvec_eq n vd v v lblr.
Proof.
  intros.
  induction n.
    simpl. auto.

    simpl in *.
    destruct vd as [h vd'].
    repeat match goal with
           | [ |- (if ?e then _ else _)]
             => destruct e
           end; auto.
Qed.

End SHeterogeneousVector.

Definition extend_denote desc (sdenote_desc : desc -> Set) : (desc+unit) -> Set :=
  (fun d => match d with inl d => sdenote_desc d | inr _ => unit end).

Fixpoint shvec_erase desc sdenote_desc (n : nat) :
  forall (lblr : fin n -> bool) (vd : svec desc n),
    shvec desc sdenote_desc n vd ->
    shvec (desc+unit) (extend_denote desc sdenote_desc) n (svec_erase lblr vd) :=
  match n as _n return
    forall (lblr : fin _n -> bool) (vd : svec desc _n),
      shvec desc sdenote_desc _n vd ->
      shvec (desc+unit) (extend_denote desc sdenote_desc) _n (svec_erase lblr vd)
  with
  | O => fun _ _ _ => tt
  | S n' => fun lblr vd =>
    match vd as _vd return
      shvec desc sdenote_desc (S n') _vd ->
      shvec (desc+unit) (extend_denote desc sdenote_desc) (S n') (svec_erase lblr _vd)
    with
    | (h, vd') => fun v =>
      let lblr' := fun (f:fin n') => lblr (shift_fin f) in
      let rest := shvec_erase desc sdenote_desc n' lblr' vd' (snd v) in
      match lblr None as _b return
        shvec (desc+unit) (extend_denote desc sdenote_desc) (S n')
          (if _b then (inl _ h, svec_erase lblr' vd') else (inr _ tt, svec_erase lblr' vd'))
      with
      | true => (fst v, rest)
      | false => (tt, rest)
      end
    end
  end.

Implicit Arguments shvec [desc n].

Implicit Arguments shvec_ith [desc n].

Implicit Arguments shvec_shift [desc n].

Implicit Arguments shvec_in [desc n].

Implicit Arguments shvec_replace_ith [desc n].

Implicit Arguments shvec_eq [desc n].

Implicit Arguments shvec_erase [desc n].

Fixpoint shvec_match {desc:Set} {n:nat} (vd:svec desc n)
  (sdenote_desc:desc->Set) (sdenote_desc':desc->Set)
  (elt_match:forall (d:desc), sdenote_desc d -> sdenote_desc' d -> bool)
  (v:shvec sdenote_desc vd) (v':shvec sdenote_desc' vd) : bool :=
  match n as _n
  return forall (vd' : svec desc _n),
         shvec sdenote_desc vd' ->
         shvec sdenote_desc' vd' ->
         bool
  with
  | O => fun _ _ _ => true
  | S n' => fun vd v v' =>
    match vd as _vd return
      @shvec desc sdenote_desc (S n') _vd ->
      @shvec desc sdenote_desc' (S n') _vd ->
      bool
    with
    | (t, vd') => fun v v' =>
      match v, v' with
      | (elt, rest), (elt', rest') =>
        andb (elt_match t elt elt')
             (shvec_match vd' sdenote_desc sdenote_desc' elt_match rest rest')
      end
    end v v'
  end vd v v'.

Fixpoint shvec_match_prop {desc:Set} {n:nat} (vd:svec desc n)
  (sdenote_desc:desc->Set) (sdenote_desc':desc->Set)
  (elt_match:forall (d:desc), sdenote_desc d -> sdenote_desc' d -> Prop)
  (v:shvec sdenote_desc vd) (v':shvec sdenote_desc' vd) : Prop :=
  match n as _n
  return forall (vd' : svec desc _n),
         shvec sdenote_desc vd' ->
         shvec sdenote_desc' vd' ->
         Prop
  with
  | O => fun _ _ _ => True
  | S n' => fun vd v v' =>
    match vd as _vd return
      @shvec desc sdenote_desc (S n') _vd ->
      @shvec desc sdenote_desc' (S n') _vd ->
      Prop
    with
    | (t, vd') => fun v v' =>
      match v, v' with
      | (elt, rest), (elt', rest') =>
        (elt_match t elt elt') /\
        (shvec_match_prop vd' sdenote_desc sdenote_desc' elt_match rest rest')
      end
    end v v'
  end vd v v'.

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

Theorem shvec_in_ith
  (desc : Set) (sdenote_desc : desc -> Set) desc_eqdec :
  forall (d : desc) (x : sdenote_desc d) (n : nat) (vd : svec desc n) v,
  shvec_in sdenote_desc desc_eqdec d x vd v ->
  exists i : fin n, ex (fun (e : d = svec_ith vd i) =>
    match e in (_ = _dd) return (sdenote_desc _dd -> Prop) with
    | Logic.eq_refl => fun x' => x' = x
    end (shvec_ith sdenote_desc vd v i)
  ).
Proof.
  intros. induction n.
  simpl in *. destruct H.
  simpl in vd. destruct vd as [vd vd'].
  simpl in v. destruct v as [v v'].
  simpl in H. destruct (desc_eqdec d vd).
  subst. intuition.
  subst. exists None. simpl. exists (Logic.eq_refl vd). reflexivity.
  specialize (IHn vd' v' H0). destruct IHn as [i' H'].
  now exists (Some i').
  specialize (IHn vd' v' H). destruct IHn as [i' H'].
  now exists (Some i').
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
