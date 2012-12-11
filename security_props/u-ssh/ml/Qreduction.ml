open BinInt
open BinPos
open Datatypes
open QArith_base
open Znumtheory

(** val coq_Z2P : coq_Z -> positive **)

let coq_Z2P = function
| Z0 -> Coq_xH
| Zpos p -> p
| Zneg p -> p

(** val coq_Qred : coq_Q -> coq_Q **)

let coq_Qred q =
  let { coq_Qnum = q1; coq_Qden = q2 } = q in
  let Coq_pair (r1, r2) = snd (coq_Zggcd q1 (Zpos q2)) in
  { coq_Qnum = r1; coq_Qden = (coq_Z2P r2) }

(** val coq_Qplus' : coq_Q -> coq_Q -> coq_Q **)

let coq_Qplus' p q =
  coq_Qred (coq_Qplus p q)

(** val coq_Qmult' : coq_Q -> coq_Q -> coq_Q **)

let coq_Qmult' p q =
  coq_Qred (coq_Qmult p q)

(** val coq_Qminus' : coq_Q -> coq_Q -> coq_Q **)

let coq_Qminus' x y =
  coq_Qred (coq_Qminus x y)

