open Datatypes
open NatOrderedType

type __ = Obj.t

(** val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let rec max n m =
  match n with
  | MlCoq.O -> m
  | MlCoq.S n' ->
    (match m with
     | MlCoq.O -> n
     | MlCoq.S m' -> MlCoq.S (max n' m'))

(** val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let rec min n m =
  match n with
  | MlCoq.O -> MlCoq.O
  | MlCoq.S n' ->
    (match m with
     | MlCoq.O -> MlCoq.O
     | MlCoq.S m' -> MlCoq.S (min n' m'))

module NatHasMinMax = 
 struct 
  (** val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let max =
    max
  
  (** val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let min =
    min
 end

module MMP = GenericMinMax.UsualMinMaxProperties(Nat_as_OT)(NatHasMinMax)

