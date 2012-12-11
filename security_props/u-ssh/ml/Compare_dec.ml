open Datatypes
open Specif

(** val zerop : MlCoq.nat -> bool **)

let zerop = function
| MlCoq.O -> true
| MlCoq.S n0 -> false

(** val lt_eq_lt_dec : MlCoq.nat -> MlCoq.nat -> bool sumor **)

let rec lt_eq_lt_dec n m =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> Coq_inleft false
     | MlCoq.S m0 -> Coq_inleft true)
  | MlCoq.S n0 ->
    (match m with
     | MlCoq.O -> Coq_inright
     | MlCoq.S m0 -> lt_eq_lt_dec n0 m0)

(** val gt_eq_gt_dec : MlCoq.nat -> MlCoq.nat -> bool sumor **)

let gt_eq_gt_dec n m =
  lt_eq_lt_dec n m

(** val le_lt_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let rec le_lt_dec n m =
  match n with
  | MlCoq.O -> true
  | MlCoq.S n0 ->
    (match m with
     | MlCoq.O -> false
     | MlCoq.S m0 -> le_lt_dec n0 m0)

(** val le_le_S_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let le_le_S_dec n m =
  le_lt_dec n m

(** val le_ge_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let le_ge_dec n m =
  le_lt_dec n m

(** val le_gt_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let le_gt_dec n m =
  le_lt_dec n m

(** val le_lt_eq_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let le_lt_eq_dec n m =
  let s = lt_eq_lt_dec n m in
  (match s with
   | Coq_inleft s0 -> s0
   | Coq_inright -> assert false (* absurd case *))

(** val le_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let le_dec n m =
  le_gt_dec n m

(** val lt_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let lt_dec n m =
  le_dec (MlCoq.S n) m

(** val gt_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let gt_dec n m =
  lt_dec m n

(** val ge_dec : MlCoq.nat -> MlCoq.nat -> bool **)

let ge_dec n m =
  le_dec m n

(** val nat_compare : MlCoq.nat -> MlCoq.nat -> comparison **)

let rec nat_compare n m =
  match n with
  | MlCoq.O ->
    (match m with
     | MlCoq.O -> Eq
     | MlCoq.S n0 -> Lt)
  | MlCoq.S n' ->
    (match m with
     | MlCoq.O -> Gt
     | MlCoq.S m' -> nat_compare n' m')

(** val nat_compare_alt : MlCoq.nat -> MlCoq.nat -> comparison **)

let nat_compare_alt n m =
  match lt_eq_lt_dec n m with
  | Coq_inleft s -> if s then Lt else Eq
  | Coq_inright -> Gt

(** val leb : MlCoq.nat -> MlCoq.nat -> bool **)

let rec leb m x =
  match m with
  | MlCoq.O -> true
  | MlCoq.S m' ->
    (match x with
     | MlCoq.O -> false
     | MlCoq.S n' -> leb m' n')

