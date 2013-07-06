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

Fixpoint svec_erase (desc : Set) (n : nat) :
  (fin n -> bool) -> svec desc n -> svec (desc + unit) n :=
  match n as _n return
    (fin _n -> bool) -> svec desc _n -> svec (desc + unit) _n
  with
  | O => fun _ _ => tt
  | S n' => fun lblr vd =>
    match vd with
    | (h, vd') =>
      let lblr' := fun (f:fin n') => lblr (shift_fin f) in
      let rest := svec_erase desc n' lblr' vd' in
      match lblr None with
      | true => (inl _ h, rest)
      | false => (inr _ tt, rest)
      end
    end
  end.

Implicit Arguments svec_ith [T n].
Implicit Arguments svec_shift [T n].
Implicit Arguments svec_erase [desc n].

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
