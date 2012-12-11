open Specif

(** val coq_O_or_S : MlCoq.nat -> MlCoq.nat sumor **)

let coq_O_or_S = function
| MlCoq.O -> Coq_inright
| MlCoq.S n0 -> Coq_inleft n0

(** val eq_nat_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let rec eq_nat_dec n m =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> true
     | MlCoq.S m0 -> false)
  | MlCoq.S n0 ->
    (match m with
     | MlCoq.O -> false
     | MlCoq.S m0 -> eq_nat_dec n0 m0)

