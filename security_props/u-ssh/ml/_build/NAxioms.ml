open NZAxioms

module type NAxioms = 
 functor (NZ:NZDomainSig') ->
 sig 
  val recursion : 'a1 -> (NZ.t -> 'a1 -> 'a1) -> NZ.t -> 'a1
 end

module type NAxiomsSig = 
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
  
  val recursion : 'a1 -> (t -> 'a1 -> 'a1) -> t -> 'a1
 end

module type NAxiomsSig' = 
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
  
  val recursion : 'a1 -> (t -> 'a1 -> 'a1) -> t -> 'a1
 end

