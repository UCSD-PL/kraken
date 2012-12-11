open Compare_dec
open Datatypes
open EqNat
open Equalities
open OrdersTac

module Nat_as_UBE : 
 sig 
  type t = MlCoq.nat
  
  val eqb : MlCoq.nat -> MlCoq.nat -> bool
 end

module Nat_as_DT : 
 sig 
  type t = MlCoq.nat
  
  val eqb : MlCoq.nat -> MlCoq.nat -> bool
  
  val eq_dec : MlCoq.nat -> MlCoq.nat -> bool
 end

module Nat_as_OT : 
 sig 
  type t = MlCoq.nat
  
  val eqb : MlCoq.nat -> MlCoq.nat -> bool
  
  val eq_dec : MlCoq.nat -> MlCoq.nat -> bool
  
  val compare : MlCoq.nat -> MlCoq.nat -> comparison
 end

module NatOrder : 
 sig 
  module TO : 
   sig 
    type t = MlCoq.nat
    
    val compare : MlCoq.nat -> MlCoq.nat -> comparison
    
    val eq_dec : MlCoq.nat -> MlCoq.nat -> bool
   end
 end

