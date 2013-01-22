(* isomorphic to nats less than n *)
Fixpoint fin (n : nat) : Type :=
  match n with
  | O => False
  | S n' => option (fin n')
  end.

Fixpoint opt_fin (bound : nat) (n : nat) : option (fin bound) :=
  match bound with
  | O => None
  | S bound' =>
    match n with
    | O => Some None
    | S n' =>
      match opt_fin bound' n' with
      | None => None
      | Some fb' => Some (Some fb')
      end
    end
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