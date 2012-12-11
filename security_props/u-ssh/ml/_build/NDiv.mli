module type NDivSpecific = 
 functor (N:NAxioms.NAxiomsSig') ->
 functor (DM:sig 
  val div : N.t -> N.t -> N.t
  
  val modulo : N.t -> N.t -> N.t
 end) ->
 sig 
  
 end

module type NDivSig = 
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
  
  val div : t -> t -> t
  
  val modulo : t -> t -> t
 end

module type NDivSig' = 
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
  
  val div : t -> t -> t
  
  val modulo : t -> t -> t
 end

module NDivPropFunct : 
 functor (N:NDivSig') ->
 functor (NP:sig 
  module OrderElts : 
   sig 
    type t = N.t
   end
  
  module OrderTac : 
   sig 
    
   end
  
  val if_zero : 'a1 -> 'a1 -> N.t -> 'a1
 end) ->
 sig 
  module ND : 
   sig 
    val div : N.t -> N.t -> N.t
    
    val modulo : N.t -> N.t -> N.t
   end
  
  module NZDivP : 
   sig 
    
   end
 end

