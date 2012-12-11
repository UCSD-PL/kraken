open Heap
open ST
open Specif

type 't coq_STsep = 't coq_ST

type 't coq_Cmd = 't coq_STsep

(** val coq_SepReturn : 'a1 -> 'a1 coq_STsep **)

let coq_SepReturn v =
  coq_STWeaken (coq_STStrengthen (coq_STReturn v))

(** val coq_SepBind :
    'a1 coq_STsep -> ('a1 -> 'a2 coq_STsep) -> 'a2 coq_STsep **)

let coq_SepBind st1 st2 =
  coq_STBind st1 st2

(** val coq_SepSeq : unit coq_STsep -> 'a1 coq_STsep -> 'a1 coq_STsep **)

let coq_SepSeq st1 st2 =
  coq_SepBind st1 (fun v -> st2)

(** val coq_SepContra : 'a1 coq_STsep **)

let coq_SepContra =
  coq_STWeaken (coq_STStrengthen coq_STContra)

(** val coq_SepFix :
    (('a1 -> 'a2 coq_STsep) -> 'a1 -> 'a2 coq_STsep) -> 'a1 -> 'a2 coq_STsep **)

let coq_SepFix f v =
  coq_STFix f v

(** val coq_SepNew : 'a1 -> ptr coq_STsep **)

let coq_SepNew v =
  coq_STWeaken (coq_STStrengthen (coq_STNew v))

(** val coq_SepFree : ptr -> unit coq_STsep **)

let coq_SepFree p =
  coq_STWeaken (coq_STStrengthen (coq_STFree p))

(** val coq_SepRead : ptr -> 'a1 coq_STsep **)

let coq_SepRead p =
  coq_STWeaken (coq_STStrengthen (coq_STRead p))

(** val coq_SepWrite : ptr -> 'a2 -> unit coq_STsep **)

let coq_SepWrite p v =
  coq_STWeaken (coq_STStrengthen (coq_STWrite p v))

(** val coq_SepStrengthen : 'a1 coq_STsep -> 'a1 coq_STsep **)

let coq_SepStrengthen st =
  coq_STWeaken (coq_STStrengthen st)

(** val coq_SepWeaken : 'a1 coq_STsep -> 'a1 coq_STsep **)

let coq_SepWeaken st =
  coq_STWeaken (coq_STStrengthen st)

(** val coq_SepFrame : 'a1 coq_STsep -> 'a1 coq_STsep **)

let coq_SepFrame st =
  coq_STWeaken (coq_STStrengthen st)

(** val coq_SepAssert : unit coq_STsep **)

let coq_SepAssert =
  coq_STWeaken (coq_STStrengthen (coq_STReturn ()))

(** val coq_SepFix2 :
    (('a1 -> 'a2 -> 'a3 coq_STsep) -> 'a1 -> 'a2 -> 'a3 coq_STsep) -> 'a1 ->
    'a2 -> 'a3 coq_STsep **)

let coq_SepFix2 f v1 v2 =
  coq_SepFix (fun self x ->
    f (fun a b -> self (Coq_existT (a, b))) (projT1 x) (projT2 x))
    (Coq_existT (v1, v2))

(** val coq_SepFix3 :
    (('a1 -> 'a2 -> 'a3 -> 'a4 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4
    coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4 coq_STsep **)

let coq_SepFix3 f v1 v2 v3 =
  coq_SepFix2 (fun self x ->
    f (fun a b c -> self (Coq_existT (a, b)) c) (projT1 x) (projT2 x))
    (Coq_existT (v1, v2)) v3

(** val coq_SepFix4 :
    (('a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4
    -> 'a5 coq_STsep) -> 'a1 -> 'a2 -> 'a3 -> 'a4 -> 'a5 coq_STsep **)

let coq_SepFix4 f v1 v2 v3 v4 =
  coq_SepFix3 (fun self x ->
    f (fun a b c d -> self (Coq_existT (a, b)) c d) (projT1 x) (projT2 x))
    (Coq_existT (v1, v2)) v3 v4

