Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexVec.

Section HeterogeneousVector.

Variable desc : Type.
Variable Instance denote_desc : Denoted desc.

Fixpoint hvec (n : nat) : vec desc n -> Type :=
  match n with
  | O => fun _ => unit
  | S n' => fun v =>
    match v with
    | (t, v') => [[ t ]] * hvec n' v'
    end
  end%type.

Fixpoint hv_nth (n : nat) (v_d : vec desc n) (v : hvec n v_d) (i : fin n)
  : [[ v_get desc n v_d i ]] :=
  match n as _n return
    forall (v_d : vec desc _n) (v : hvec _n v_d) (i : fin _n), [[ v_get desc _n v_d i ]]
  with
  | O => fun v_d v i => match i with end
  | S n' => fun (v_d : desc * vec desc n') (v : hvec (S n') v_d) i =>
    match v_d as _v_d return
      forall (v : hvec (S n') _v_d) (i : fin (S n')), [[ v_get desc (S n') _v_d i ]]
    with
    | (t, v_d') => fun (v : [[ t ]] * hvec n' v_d') (i : fin (S n')) =>
      match i with
      | None => fst v
      | Some i' => hv_nth n' v_d' (snd v) i'
      end
    end v i
  end v_d v i.

End HeterogeneousVector.