open Heap
open Hprop

type __ = Obj.t

type hpre = hprop

type 't hpost = __

type 't coq_ST =  't STImpl.axiom_ST 

(** val coq_STReturn : 'a1 -> 'a1 coq_ST **)

let coq_STReturn = STImpl.axiom_STReturn

(** val coq_STBind : 'a1 coq_ST -> ('a1 -> 'a2 coq_ST) -> 'a2 coq_ST **)

let coq_STBind = STImpl.axiom_STBind

(** val coq_STContra : 'a1 coq_ST **)

let coq_STContra = STImpl.axiom_STContra

(** val coq_STFix :
    (('a1 -> 'a2 coq_ST) -> 'a1 -> 'a2 coq_ST) -> 'a1 -> 'a2 coq_ST **)

let coq_STFix = STImpl.axiom_STFix

(** val coq_STNew : 'a1 -> ptr coq_ST **)

let coq_STNew = STImpl.axiom_STNew

(** val coq_STFree : ptr -> unit coq_ST **)

let coq_STFree = STImpl.axiom_STFree

(** val coq_STRead : ptr -> 'a1 coq_ST **)

let coq_STRead = STImpl.axiom_STRead

(** val coq_STWrite : ptr -> 'a2 -> unit coq_ST **)

let coq_STWrite = STImpl.axiom_STWrite

(** val coq_STStrengthen : 'a1 coq_ST -> 'a1 coq_ST **)

let coq_STStrengthen = STImpl.axiom_STStrengthen

(** val coq_STWeaken : 'a1 coq_ST -> 'a1 coq_ST **)

let coq_STWeaken = STImpl.axiom_STWeaken

