open BinInt
open BinPos
open Datatypes
open QArith_base
open Qreduction
open Specif

type __ = Obj.t

type coq_Qc =
  coq_Q
  (* singleton inductive, whose constructor was Qcmake *)

val coq_Qc_rect : (coq_Q -> __ -> 'a1) -> coq_Qc -> 'a1

val coq_Qc_rec : (coq_Q -> __ -> 'a1) -> coq_Qc -> 'a1

val this : coq_Qc -> coq_Q

val coq_Q2Qc : coq_Q -> coq_Qc

val coq_Qccompare : coq_Qc -> coq_Qc -> comparison

val coq_Qc_eq_dec : coq_Qc -> coq_Qc -> bool

val coq_Qcplus : coq_Qc -> coq_Qc -> coq_Qc

val coq_Qcmult : coq_Qc -> coq_Qc -> coq_Qc

val coq_Qcopp : coq_Qc -> coq_Qc

val coq_Qcminus : coq_Qc -> coq_Qc -> coq_Qc

val coq_Qcinv : coq_Qc -> coq_Qc

val coq_Qcdiv : coq_Qc -> coq_Qc -> coq_Qc

val coq_Qc_dec : coq_Qc -> coq_Qc -> bool sumor

val coq_Qclt_le_dec : coq_Qc -> coq_Qc -> bool

val coq_Qcpower : coq_Qc -> MlCoq.nat -> coq_Qc

val coq_Qc_eq_bool : coq_Qc -> coq_Qc -> bool

