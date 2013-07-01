Require Import ReflexFin.

Section SVector.

Variable T : Set.

Fixpoint svec (n : nat) : Set :=
  match n with
  | O => unit
  | S n' => T * svec n'
  end%type.

Fixpoint svec_ith (n : nat) : svec n -> fin n -> T :=
  match n with
  | O => fun _ idx => match idx with end
  | S n' => fun v idx =>
    match idx with
    | None => fst v
    | Some idx' => svec_ith n' (snd v) idx'
    end
  end.

Fixpoint svec_shift (n : nat) (e : T) : svec n -> svec (S n) :=
  match n with
  | O    => fun _ => (e, tt)
  | S n' => fun v =>
    (fst v, svec_shift n' e (snd v))
  end.

End SVector.

Implicit Arguments svec_ith [T n].
Implicit Arguments svec_shift [T n].

Section Vector.

Variable T : Type.

Fixpoint vec (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => T * vec n'
  end%type.

Fixpoint vec_ith (n : nat) : vec n -> fin n -> T :=
  match n with
  | O => fun _ idx => match idx with end
  | S n' => fun v idx =>
    match idx with
    | None => fst v
    | Some idx' => vec_ith n' (snd v) idx'
    end
  end.

End Vector.

Implicit Arguments vec_ith [T n].
