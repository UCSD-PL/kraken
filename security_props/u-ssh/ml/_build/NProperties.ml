open NSub
open OrdersTac

module type NPropSig = 
 NSubPropFunct

module NPropFunct = 
 functor (N:NAxioms.NAxiomsSig) ->
 struct 
  module OrderElts = 
   struct 
    type t = N.t
   end
  
  module OrderTac = MakeOrderTac(OrderElts)
  
  (** val if_zero : 'a1 -> 'a1 -> N.t -> 'a1 **)
  
  let if_zero a b n =
    N.recursion a (fun x x0 -> b) n
 end

