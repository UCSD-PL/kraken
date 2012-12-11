(** val pred : MlCoq.nat -> MlCoq.nat **)

let pred n = match n with
| MlCoq.O -> n
| MlCoq.S u -> u

(** val plus : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let rec plus n m =
  match n with
  | MlCoq.O -> m
  | MlCoq.S p -> MlCoq.S (plus p m)

(** val mult : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let rec mult n m =
  match n with
  | MlCoq.O -> MlCoq.O
  | MlCoq.S p -> plus m (mult p m)

(** val minus : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let rec minus n m =
  match n with
  | MlCoq.O -> n
  | MlCoq.S k ->
    (match m with
     | MlCoq.O -> n
     | MlCoq.S l -> minus k l)

