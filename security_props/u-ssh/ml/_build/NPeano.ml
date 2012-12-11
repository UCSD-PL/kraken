open Compare_dec
open MinMax
open NDiv
open NProperties
open Peano

module NPeanoAxiomsMod = 
 struct 
  (** val recursion :
      'a1 -> (MlCoq.nat -> 'a1 -> 'a1) -> MlCoq.nat -> 'a1 **)
  
  let rec recursion x f = function
  | MlCoq.O -> x
  | MlCoq.S n0 -> f n0 (recursion x f n0)
  
  type t = MlCoq.nat
  
  (** val zero : MlCoq.nat **)
  
  let zero =
    MlCoq.O
  
  (** val succ : MlCoq.nat -> MlCoq.nat **)
  
  let succ x =
    MlCoq.S x
  
  (** val pred : MlCoq.nat -> MlCoq.nat **)
  
  let pred =
    pred
  
  (** val add : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let add =
    plus
  
  (** val sub : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let sub =
    minus
  
  (** val mul : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let mul =
    mult
  
  (** val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let min =
    min
  
  (** val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let max =
    max
 end

module NPeanoPropMod = NPropFunct(NPeanoAxiomsMod)

(** val divF :
    (MlCoq.nat -> MlCoq.nat -> MlCoq.nat) -> MlCoq.nat -> MlCoq.nat ->
    MlCoq.nat **)

let divF div0 x y =
  if leb y x then MlCoq.S (div0 (minus x y) y) else MlCoq.O

(** val modF :
    (MlCoq.nat -> MlCoq.nat -> MlCoq.nat) -> MlCoq.nat -> MlCoq.nat ->
    MlCoq.nat **)

let modF mod0 x y =
  if leb y x then mod0 (minus x y) y else x

(** val initF : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let initF x x0 =
  MlCoq.O

(** val loop : ('a1 -> 'a1) -> 'a1 -> MlCoq.nat -> 'a1 **)

let rec loop f i = function
| MlCoq.O -> i
| MlCoq.S n0 -> f (loop f i n0)

(** val div : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let div x y =
  loop divF initF x x y

(** val modulo : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)

let modulo x y =
  loop modF initF x x y

module NDivMod = 
 struct 
  (** val recursion :
      'a1 -> (MlCoq.nat -> 'a1 -> 'a1) -> MlCoq.nat -> 'a1 **)
  
  let rec recursion x f = function
  | MlCoq.O -> x
  | MlCoq.S n0 -> f n0 (recursion x f n0)
  
  type t = MlCoq.nat
  
  (** val zero : MlCoq.nat **)
  
  let zero =
    MlCoq.O
  
  (** val succ : MlCoq.nat -> MlCoq.nat **)
  
  let succ x =
    MlCoq.S x
  
  (** val pred : MlCoq.nat -> MlCoq.nat **)
  
  let pred =
    pred
  
  (** val add : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let add =
    plus
  
  (** val sub : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let sub =
    minus
  
  (** val mul : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let mul =
    mult
  
  (** val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let min =
    min
  
  (** val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let max =
    max
  
  (** val div : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let div =
    div
  
  (** val modulo : MlCoq.nat -> MlCoq.nat -> MlCoq.nat **)
  
  let modulo =
    modulo
 end

module NDivPropMod = NDivPropFunct(NDivMod)(NPeanoPropMod)

