Fixpoint fin (n : nat) : Type :=
  match n with
  | O => False
  | S n' => option (fin n')
  end.
