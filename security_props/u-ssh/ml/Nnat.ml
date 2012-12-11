open BinNat
open BinPos

(** val nat_of_N : coq_N -> MlCoq.nat **)

let nat_of_N = function
| N0 -> MlCoq.O
| Npos p -> nat_of_P p

(** val coq_N_of_nat : MlCoq.nat -> coq_N **)

let coq_N_of_nat = function
| MlCoq.O -> N0
| MlCoq.S n' -> Npos (coq_P_of_succ_nat n')

