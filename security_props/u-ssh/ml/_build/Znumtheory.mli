open BinInt
open BinPos
open Datatypes
open Peano
open Specif
open Wf_Z
open ZArith_dec
open Zdiv
open Zorder

type __ = Obj.t

val coq_Zdivide_dec : coq_Z -> coq_Z -> bool

val coq_Zis_gcd_rect :
  coq_Z -> coq_Z -> coq_Z -> (__ -> __ -> __ -> 'a1) -> 'a1

val coq_Zis_gcd_rec :
  coq_Z -> coq_Z -> coq_Z -> (__ -> __ -> __ -> 'a1) -> 'a1

type coq_Euclid =
| Euclid_intro of coq_Z * coq_Z * coq_Z

val coq_Euclid_rect :
  coq_Z -> coq_Z -> (coq_Z -> coq_Z -> coq_Z -> __ -> __ -> 'a1) ->
  coq_Euclid -> 'a1

val coq_Euclid_rec :
  coq_Z -> coq_Z -> (coq_Z -> coq_Z -> coq_Z -> __ -> __ -> 'a1) ->
  coq_Euclid -> 'a1

val euclid_rec :
  coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z ->
  coq_Euclid

val euclid : coq_Z -> coq_Z -> coq_Euclid

val prime_rect : coq_Z -> (__ -> __ -> 'a1) -> 'a1

val prime_rec : coq_Z -> (__ -> __ -> 'a1) -> 'a1

val coq_Pgcdn : MlCoq.nat -> positive -> positive -> positive

val coq_Pgcd : positive -> positive -> positive

val coq_Zgcd : coq_Z -> coq_Z -> coq_Z

val coq_Zgcd_spec : coq_Z -> coq_Z -> coq_Z

val rel_prime_dec : coq_Z -> coq_Z -> bool

val prime_dec_aux : coq_Z -> coq_Z -> bool

val prime_dec : coq_Z -> bool

val coq_Pggcdn :
  MlCoq.nat -> positive -> positive -> (positive, (positive, positive) prod)
  prod

val coq_Pggcd :
  positive -> positive -> (positive, (positive, positive) prod) prod

val coq_Zggcd : coq_Z -> coq_Z -> (coq_Z, (coq_Z, coq_Z) prod) prod

