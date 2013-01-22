Require Import ReflexFin.

Section Vector.

Variable T : Type.

Fixpoint vec (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => T * vec n'
  end%type.

Fixpoint v_get (n : nat) : vec n -> fin n -> T :=
  match n with
  | O => fun _ idx => match idx with end
  | S n' => fun v idx =>
    match idx with
    | None => fst v
    | Some idx' => v_get n' (snd v) idx'
    end
  end.

End Vector.

Implicit Arguments v_get [T n].
