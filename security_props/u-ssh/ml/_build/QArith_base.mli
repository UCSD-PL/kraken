open BinInt
open BinPos
open Datatypes
open Ring_theory
open Specif
open ZArith_dec
open Zbool

type coq_Q = { coq_Qnum : coq_Z; coq_Qden : positive }

val coq_Q_rect : (coq_Z -> positive -> 'a1) -> coq_Q -> 'a1

val coq_Q_rec : (coq_Z -> positive -> 'a1) -> coq_Q -> 'a1

val coq_Qnum : coq_Q -> coq_Z

val coq_Qden : coq_Q -> positive

val inject_Z : coq_Z -> coq_Q

val coq_Qcompare : coq_Q -> coq_Q -> comparison

val coq_Qeq_dec : coq_Q -> coq_Q -> bool

val coq_Qeq_bool : coq_Q -> coq_Q -> bool

val coq_Qle_bool : coq_Q -> coq_Q -> bool

val coq_Qplus : coq_Q -> coq_Q -> coq_Q

val coq_Qmult : coq_Q -> coq_Q -> coq_Q

val coq_Qopp : coq_Q -> coq_Q

val coq_Qminus : coq_Q -> coq_Q -> coq_Q

val coq_Qinv : coq_Q -> coq_Q

val coq_Qdiv : coq_Q -> coq_Q -> coq_Q

val coq_Q_dec : coq_Q -> coq_Q -> bool sumor

val coq_Qlt_le_dec : coq_Q -> coq_Q -> bool

val coq_Qpower_positive : coq_Q -> positive -> coq_Q

val coq_Qpower : coq_Q -> coq_Z -> coq_Q

