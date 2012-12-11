open Equalities
open NZAxioms

module type DivMod = 
 functor (T:Typ) ->
 sig 
  val div : T.t -> T.t -> T.t
  
  val modulo : T.t -> T.t -> T.t
 end

module type DivModNotation = 
 functor (T:Typ) ->
 functor (NZ:sig 
  val div : T.t -> T.t -> T.t
  
  val modulo : T.t -> T.t -> T.t
 end) ->
 sig 
  
 end

module type DivMod' = 
 functor (T:Typ) ->
 sig 
  val div : T.t -> T.t -> T.t
  
  val modulo : T.t -> T.t -> T.t
 end

module type NZDivCommon = 
 functor (NZ:NZAxiomsSig') ->
 functor (DM:sig 
  val div : NZ.t -> NZ.t -> NZ.t
  
  val modulo : NZ.t -> NZ.t -> NZ.t
 end) ->
 sig 
  
 end

module type NZDivSpecific = 
 functor (NZ:NZOrdAxiomsSig') ->
 functor (DM:sig 
  val div : NZ.t -> NZ.t -> NZ.t
  
  val modulo : NZ.t -> NZ.t -> NZ.t
 end) ->
 sig 
  
 end

module type NZDiv = 
 functor (NZ:NZOrdAxiomsSig) ->
 sig 
  val div : NZ.t -> NZ.t -> NZ.t
  
  val modulo : NZ.t -> NZ.t -> NZ.t
 end

module type NZDiv' = 
 functor (NZ:NZOrdAxiomsSig) ->
 sig 
  val div : NZ.t -> NZ.t -> NZ.t
  
  val modulo : NZ.t -> NZ.t -> NZ.t
 end

module NZDivPropFunct = 
 functor (NZ:NZOrdAxiomsSig') ->
 functor (NZP:sig 
  module OrderElts : 
   sig 
    type t = NZ.t
   end
  
  module OrderTac : 
   sig 
    
   end
 end) ->
 functor (NZD:sig 
  val div : NZ.t -> NZ.t -> NZ.t
  
  val modulo : NZ.t -> NZ.t -> NZ.t
 end) ->
 struct 
  
 end

