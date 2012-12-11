open Datatypes
open Equalities

module type ZeroSuccPred = 
 functor (T:Typ) ->
 sig 
  val zero : T.t
  
  val succ : T.t -> T.t
  
  val pred : T.t -> T.t
 end

module type ZeroSuccPredNotation = 
 functor (T:Typ) ->
 functor (NZ:sig 
  val zero : T.t
  
  val succ : T.t -> T.t
  
  val pred : T.t -> T.t
 end) ->
 sig 
  
 end

module type ZeroSuccPred' = 
 functor (T:Typ) ->
 sig 
  val zero : T.t
  
  val succ : T.t -> T.t
  
  val pred : T.t -> T.t
 end

module type IsNZDomain = 
 functor (E:Eq') ->
 functor (NZ:sig 
  val zero : E.t
  
  val succ : E.t -> E.t
  
  val pred : E.t -> E.t
 end) ->
 sig 
  
 end

module type NZDomainSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type NZDomainSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type AddSubMul = 
 functor (T:Typ) ->
 sig 
  val add : T.t -> T.t -> T.t
  
  val sub : T.t -> T.t -> T.t
  
  val mul : T.t -> T.t -> T.t
 end

module type AddSubMulNotation = 
 functor (T:Typ) ->
 functor (NZ:sig 
  val add : T.t -> T.t -> T.t
  
  val sub : T.t -> T.t -> T.t
  
  val mul : T.t -> T.t -> T.t
 end) ->
 sig 
  
 end

module type AddSubMul' = 
 functor (T:Typ) ->
 sig 
  val add : T.t -> T.t -> T.t
  
  val sub : T.t -> T.t -> T.t
  
  val mul : T.t -> T.t -> T.t
 end

module type IsAddSubMul = 
 functor (E:NZDomainSig') ->
 functor (NZ:sig 
  val add : E.t -> E.t -> E.t
  
  val sub : E.t -> E.t -> E.t
  
  val mul : E.t -> E.t -> E.t
 end) ->
 sig 
  
 end

module type NZBasicFunsSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
 end

module type NZBasicFunsSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
 end

module type NZAxiomsSig = 
 NZBasicFunsSig

module type NZAxiomsSig' = 
 NZBasicFunsSig'

module type NZOrd = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type NZOrd' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type IsNZOrd = 
 functor (NZ:NZOrd') ->
 sig 
  
 end

module type NZOrdSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type NZOrdSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
 end

module type NZOrdAxiomsSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
  
  val max : t -> t -> t
  
  val min : t -> t -> t
 end

module type NZOrdAxiomsSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
  
  val max : t -> t -> t
  
  val min : t -> t -> t
 end

module type NZDecOrdSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val compare : t -> t -> comparison
 end

module type NZDecOrdSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val compare : t -> t -> comparison
 end

module type NZDecOrdAxiomsSig = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
  
  val max : t -> t -> t
  
  val min : t -> t -> t
  
  val compare : t -> t -> comparison
 end

module type NZDecOrdAxiomsSig' = 
 sig 
  type t 
  
  val zero : t
  
  val succ : t -> t
  
  val pred : t -> t
  
  val add : t -> t -> t
  
  val sub : t -> t -> t
  
  val mul : t -> t -> t
  
  val max : t -> t -> t
  
  val min : t -> t -> t
  
  val compare : t -> t -> comparison
 end

