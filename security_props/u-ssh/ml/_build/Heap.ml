open Axioms
open BinInt
open BinPos
open Datatypes
open PermModel
open QArith_base
open Qcanon

type axiom_ptr = HeapImpl.axiom_ptr

type ptr = axiom_ptr

(** val axiom_ptr_eq_dec : ptr -> ptr -> bool **)

let axiom_ptr_eq_dec = HeapImpl.axiom_ptr_eq_dec

(** val ptr_eq_dec : ptr -> ptr -> bool **)

let ptr_eq_dec =
  axiom_ptr_eq_dec

type hval = (dynamic, perm) prod

type heap = ptr -> hval option

(** val coq_val : hval -> dynamic **)

let coq_val v =
  fst v

(** val frac : hval -> perm **)

let frac v =
  snd v

(** val hval_plus : hval -> hval -> hval option **)

let hval_plus v1 v2 =
  match perm_plus (frac v1) (frac v2) with
  | Some v1v2 -> Some (Coq_pair ((coq_val v1), v1v2))
  | None -> None

(** val hvalo_plus : hval option -> hval option -> hval option **)

let hvalo_plus v1 v2 =
  match v1 with
  | Some v1' ->
    (match v2 with
     | Some v2' -> hval_plus v1' v2'
     | None -> v1)
  | None -> v2

(** val ofrac : hval option -> perm **)

let ofrac = function
| Some v' -> frac v'
| None -> coq_Q2Qc { coq_Qnum = Z0; coq_Qden = Coq_xH }

(** val empty : heap **)

let empty x =
  None

(** val singleton : ptr -> hval -> heap **)

let singleton p v p' =
  if ptr_eq_dec p' p then Some v else None

(** val read : heap -> ptr -> hval option **)

let read h p =
  h p

(** val write : heap -> ptr -> hval -> heap **)

let write h p v p' =
  if ptr_eq_dec p' p then Some v else h p'

(** val free : heap -> ptr -> heap **)

let free h p p' =
  if ptr_eq_dec p' p then None else h p'

(** val join : heap -> heap -> heap **)

let join h1 h2 p =
  hvalo_plus (h1 p) (h2 p)

