open BinInt
open Datatypes
open Specif

(** val coq_Ztrichotomy_inf : coq_Z -> coq_Z -> bool sumor **)

let coq_Ztrichotomy_inf m n =
  let x = coq_Zcompare m n in
  (match x with
   | Eq -> Coq_inleft false
   | Lt -> Coq_inleft true
   | Gt -> Coq_inright)

