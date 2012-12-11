open Datatypes

val string_rect :
  'a1 -> (MlCoq.ascii -> MlCoq.ascii list -> 'a1 -> 'a1) -> MlCoq.ascii list
  -> 'a1

val string_rec :
  'a1 -> (MlCoq.ascii -> MlCoq.ascii list -> 'a1 -> 'a1) -> MlCoq.ascii list
  -> 'a1

val string_dec : MlCoq.ascii list -> MlCoq.ascii list -> bool

val append : MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.ascii list

val length : MlCoq.ascii list -> MlCoq.nat

val get : MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii option

val substring :
  MlCoq.nat -> MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list

val prefix : MlCoq.ascii list -> MlCoq.ascii list -> bool

val index :
  MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.nat option

val findex : MlCoq.nat -> MlCoq.ascii list -> MlCoq.ascii list -> MlCoq.nat

val coq_HelloWorld : MlCoq.ascii list

