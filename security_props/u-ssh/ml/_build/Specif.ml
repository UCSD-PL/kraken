open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a coq_sig =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val sig_rect : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2 **)

let sig_rect f s =
  f s __

(** val sig_rec : ('a1 -> __ -> 'a2) -> 'a1 -> 'a2 **)

let sig_rec f s =
  f s __

type 'a sig2 =
  'a
  (* singleton inductive, whose constructor was exist2 *)

(** val sig2_rect : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2 **)

let sig2_rect f s =
  f s __ __

(** val sig2_rec : ('a1 -> __ -> __ -> 'a2) -> 'a1 sig2 -> 'a2 **)

let sig2_rec f s =
  f s __ __

type ('a, 'p) sigT =
| Coq_existT of 'a * 'p

(** val sigT_rect : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3 **)

let sigT_rect f = function
| Coq_existT (x, x0) -> f x x0

(** val sigT_rec : ('a1 -> 'a2 -> 'a3) -> ('a1, 'a2) sigT -> 'a3 **)

let sigT_rec f = function
| Coq_existT (x, x0) -> f x x0

type ('a, 'p, 'q) sigT2 =
| Coq_existT2 of 'a * 'p * 'q

(** val sigT2_rect :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4 **)

let sigT2_rect f = function
| Coq_existT2 (x, x0, x1) -> f x x0 x1

(** val sigT2_rec :
    ('a1 -> 'a2 -> 'a3 -> 'a4) -> ('a1, 'a2, 'a3) sigT2 -> 'a4 **)

let sigT2_rec f = function
| Coq_existT2 (x, x0, x1) -> f x x0 x1

(** val proj1_sig : 'a1 -> 'a1 **)

let proj1_sig e =
  e

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| Coq_existT (a, p) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| Coq_existT (x0, h) -> h

(** val sig_of_sigT : ('a1, __) sigT -> 'a1 **)

let sig_of_sigT = function
| Coq_existT (x0, _) -> x0

(** val sigT_of_sig : 'a1 -> ('a1, __) sigT **)

let sigT_of_sig x =
  Coq_existT (x, __)

(** val sumbool_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> 'a1 **)

let sumbool_rect f f0 = function
| true -> f __
| false -> f0 __

(** val sumbool_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> 'a1 **)

let sumbool_rec f f0 = function
| true -> f __
| false -> f0 __

type 'a sumor =
| Coq_inleft of 'a
| Coq_inright

(** val sumor_rect : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2 **)

let sumor_rect f f0 = function
| Coq_inleft x -> f x
| Coq_inright -> f0 __

(** val sumor_rec : ('a1 -> 'a2) -> (__ -> 'a2) -> 'a1 sumor -> 'a2 **)

let sumor_rec f f0 = function
| Coq_inleft x -> f x
| Coq_inright -> f0 __

(** val coq_Choice : ('a1 -> 'a2) -> ('a1 -> 'a2) **)

let coq_Choice h z =
  h z

(** val coq_Choice2 :
    ('a1 -> ('a2, 'a3) sigT) -> ('a1 -> 'a2, 'a1 -> 'a3) sigT **)

let coq_Choice2 h =
  Coq_existT ((fun z -> projT1 (h z)), (fun z ->
    let s = h z in let Coq_existT (x, r) = s in r))

(** val bool_choice : ('a1 -> bool) -> ('a1 -> bool) **)

let bool_choice h z =
  if h z then true else false

(** val dependent_choice : ('a1 -> 'a1) -> 'a1 -> (MlCoq.nat -> 'a1) **)

let rec dependent_choice h x0 = function
| MlCoq.O -> x0
| MlCoq.S n' -> h (dependent_choice h x0 n')

type 'a coq_Exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val except : __ -> 'a1 **)

let except _ =
  assert false (* absurd case *)

(** val absurd_set : __ -> 'a1 **)

let absurd_set _ =
  assert false (* absurd case *)

