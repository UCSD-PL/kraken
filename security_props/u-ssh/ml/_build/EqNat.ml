(** val eq_nat_decide : MlCoq.nat -> MlCoq.nat -> bool **)

let rec eq_nat_decide n m =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> true
     | MlCoq.S n0 -> false)
  | MlCoq.S n0 ->
    (match m with
     | MlCoq.O -> false
     | MlCoq.S n1 -> eq_nat_decide n0 n1)

(** val beq_nat : MlCoq.nat -> MlCoq.nat -> bool **)

let rec beq_nat n m =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> true
     | MlCoq.S n0 -> false)
  | MlCoq.S n1 ->
    (match m with
     | MlCoq.O -> false
     | MlCoq.S m1 -> beq_nat n1 m1)

