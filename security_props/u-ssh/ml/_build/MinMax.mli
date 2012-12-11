open Datatypes
open NatOrderedType

type __ = Obj.t

val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat

val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat

module NatHasMinMax : 
 sig 
  val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
  
  val min : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
 end

module MMP : 
 sig 
  module OT : 
   sig 
    type t = MlCoq.nat
    
    val compare : MlCoq.nat -> MlCoq.nat -> comparison
    
    val eq_dec : MlCoq.nat -> MlCoq.nat -> bool
   end
  
  module T : 
   sig 
    
   end
  
  module ORev : 
   sig 
    type t = MlCoq.nat
   end
  
  module MRev : 
   sig 
    val max : MlCoq.nat -> MlCoq.nat -> MlCoq.nat
   end
  
  module MPRev : 
   sig 
    module T : 
     sig 
      
     end
   end
  
  module P : 
   sig 
    val max_case_strong :
      MlCoq.nat -> MlCoq.nat -> (MlCoq.nat -> MlCoq.nat -> __ -> 'a1 -> 'a1)
      -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val max_case :
      MlCoq.nat -> MlCoq.nat -> (MlCoq.nat -> MlCoq.nat -> __ -> 'a1 -> 'a1)
      -> 'a1 -> 'a1 -> 'a1
    
    val max_dec : MlCoq.nat -> MlCoq.nat -> bool
    
    val min_case_strong :
      MlCoq.nat -> MlCoq.nat -> (MlCoq.nat -> MlCoq.nat -> __ -> 'a1 -> 'a1)
      -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
    
    val min_case :
      MlCoq.nat -> MlCoq.nat -> (MlCoq.nat -> MlCoq.nat -> __ -> 'a1 -> 'a1)
      -> 'a1 -> 'a1 -> 'a1
    
    val min_dec : MlCoq.nat -> MlCoq.nat -> bool
   end
  
  val max_case_strong :
    MlCoq.nat -> MlCoq.nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val max_case : MlCoq.nat -> MlCoq.nat -> 'a1 -> 'a1 -> 'a1
  
  val max_dec : MlCoq.nat -> MlCoq.nat -> bool
  
  val min_case_strong :
    MlCoq.nat -> MlCoq.nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1
  
  val min_case : MlCoq.nat -> MlCoq.nat -> 'a1 -> 'a1 -> 'a1
  
  val min_dec : MlCoq.nat -> MlCoq.nat -> bool
 end

