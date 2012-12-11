open Compare_dec
open MinMax
open NDiv
open NProperties
open Peano

module NPeanoAxiomsMod : 
 sig 
  val recursion : 'a1 -> (MlCoq.nat -> 'a1 -> 'a1) -> MlCoq.nat -> 'a1
  
  type t = MlCoq.nat
  
  val zero : MlCoq.nat
  
  val succ : MlCoq.nat -> MlCoq.nat
  
  val pred : MlCoq.nat -> MlCoq.nat
  
  val add : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val sub : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val mul : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
 end

module NPeanoPropMod : 
 sig 
  module OrderElts : 
   sig 
    type t = MlCoq.nat
   end
  
  module OrderTac : 
   sig 
    
   end
  
  val if_zero : 'a1 -> 'a1 -> MlCoq.nat -> 'a1
 end

val divF :
  (MlCoq.nat -> MlCoq.nat -> MlCoq.nat) -> MlCoq.nat -> MlCoq.nat ->
  MlCoq.nat

val modF :
  (MlCoq.nat -> MlCoq.nat -> MlCoq.nat) -> MlCoq.nat -> MlCoq.nat ->
  MlCoq.nat

val initF : MlCoq.nat -> MlCoq.nat -> MlCoq.nat

val loop : ('a1 -> 'a1) -> 'a1 -> MlCoq.nat -> 'a1

val div : MlCoq.nat -> MlCoq.nat -> MlCoq.nat

val modulo : MlCoq.nat -> MlCoq.nat -> MlCoq.nat

module NDivMod : 
 sig 
  val recursion : 'a1 -> (MlCoq.nat -> 'a1 -> 'a1) -> MlCoq.nat -> 'a1
  
  type t = MlCoq.nat
  
  val zero : MlCoq.nat
  
  val succ : MlCoq.nat -> MlCoq.nat
  
  val pred : MlCoq.nat -> MlCoq.nat
  
  val add : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val sub : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val mul : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val div : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val modulo : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
 end

module NDivPropMod : 
 sig 
  module ND : 
   sig 
    val div : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
    
    val modulo : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
   end
  
  module NZDivP : 
   sig 
    
   end
 end

