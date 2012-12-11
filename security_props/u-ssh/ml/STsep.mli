open Heap
open ST
open Specif

type 't coq_STsep = 't coq_ST

type 't coq_Cmd = 't coq_STsep

val coq_SepReturn : 'a1 -> 'a1 coq_STsep

val coq_SepBind : 'a1 coq_STsep -> ('a1 -> 'a2 coq_STsep) -> 'a2 coq_STsep

val coq_SepSeq : unit coq_STsep -> 'a1 coq_STsep -> 'a1 coq_STsep

val coq_SepContra : 'a1 coq_STsep

val coq_SepFix :
  (('a1 -> 'a2 coq_STsep) -> 'a1 -> 'a2 coq_STsep) -> 'a1 -> 'a2 coq_STsep

val coq_SepNew : 'a1 -> ptr coq_STsep

val coq_SepFree : ptr -> unit coq_STsep

val coq_SepRead : ptr -> 'a1 coq_STsep

val coq_SepWrite : ptr -> 'a2 -> unit coq_STsep

val coq_SepStrengthen : 'a1 coq_STsep -> 'a1 coq_STsep

val coq_SepWeaken : 'a1 coq_STsep -> 'a1 coq_STsep

val coq_SepFrame : 'a1 coq_STsep -> 'a1 coq_STsep

val coq_SepAssert : unit coq_STsep

val coq_SepFix2 :
  (('a1 -> 'a2 -> 'a3 coq_STsep) -> 'a1 -> 'a2 -> 'a3 coq_STsep) -> 'a1 ->
  'a2 -> 'a3 coq_STsep

val coq_SepFix3 :
  (('a1 -> 'a2 -> 'a3 -> 'a4 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4
  coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4 coq_STsep

val coq_SepFix4 :
  (('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4 ->
  'a5 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 coq_STsep

