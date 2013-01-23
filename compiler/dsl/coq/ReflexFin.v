Require Import Arith.

(* isomorphic to nats less than n *)
Fixpoint fin (n : nat) : Set :=
  match n with
  | O => False
  | S n' => option (fin n')
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

Fixpoint opt_fin (bound : nat) (n : nat)
  : {f : fin bound & nat_of_fin f = n } + { n >= bound } :=
  let ret b n := { f : fin b & nat_of_fin f = n } + { n >= b } in
  match bound as _bound return ret _bound n with
  | O => inright _ (le_0_n _)
  | S bound' =>
    match n as _n return ret (S bound') _n with
    | O => inleft _ (existT _ None (eq_refl O))
    | S n' =>
      match opt_fin bound' n' with
      | inleft (existT f' eq') =>
        inleft _ (existT _ (Some f') (eq_ind_r (fun n => S n = S n') (eq_refl (S n')) eq'))
      | inright pf => inright _ (le_n_S _ _ pf)
      end
    end
  end.
