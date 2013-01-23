Require Import ReflexFin.

Section SVector.

Variable T : Set.

Check (unit * unit)%type.

Fixpoint svec (n : nat) : Set :=
  match n with
  | O => unit
  | S n' => T * svec n'
  end%type.

Fixpoint sv_get (n : nat) : svec n -> fin n -> T :=
  match n with
  | O => fun _ idx => match idx with end
  | S n' => fun v idx =>
    match idx with
    | None => fst v
    | Some idx' => sv_get n' (snd v) idx'
    end
  end.

End SVector.

Implicit Arguments sv_get [T n].

(* keep that in case... *)

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
