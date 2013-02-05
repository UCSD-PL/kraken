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

End SHeterogeneousVector.

Implicit Arguments shvec [desc n].

Implicit Arguments shvec_ith [desc n].

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
