open Heap
open Hprop

type __ = Obj.t

type hpre = hprop

type 't hpost = __

type 't coq_ST =  't STImpl.axiom_ST 

val coq_STReturn : 'a1 -> 'a1 coq_ST

val coq_STBind : 'a1 coq_ST -> ('a1 -> 'a2 coq_ST) -> 'a2 coq_ST

val coq_STContra : 'a1 coq_ST

val coq_STFix :
  (('a1 -> 'a2 coq_ST) -> 'a1 -> 'a2 coq_ST) -> 'a1 -> 'a2 coq_ST

val coq_STNew : 'a1 -> ptr coq_ST

val coq_STFree : ptr -> unit coq_ST

val coq_STRead : ptr -> 'a1 coq_ST

val coq_STWrite : ptr -> 'a2 -> unit coq_ST

val coq_STStrengthen : 'a1 coq_ST -> 'a1 coq_ST

val coq_STWeaken : 'a1 coq_ST -> 'a1 coq_ST

