open Datatypes
open Specif

val zerop : MlCoq.nat -> bool

val lt_eq_lt_dec : MlCoq.nat -> MlCoq.nat -> bool sumor

val gt_eq_gt_dec : MlCoq.nat -> MlCoq.nat -> bool sumor

val le_lt_dec : MlCoq.nat -> MlCoq.nat -> bool

val le_le_S_dec : MlCoq.nat -> MlCoq.nat -> bool

val le_ge_dec : MlCoq.nat -> MlCoq.nat -> bool

val le_gt_dec : MlCoq.nat -> MlCoq.nat -> bool

val le_lt_eq_dec : MlCoq.nat -> MlCoq.nat -> bool

val le_dec : MlCoq.nat -> MlCoq.nat -> bool

val lt_dec : MlCoq.nat -> MlCoq.nat -> bool

val gt_dec : MlCoq.nat -> MlCoq.nat -> bool

val ge_dec : MlCoq.nat -> MlCoq.nat -> bool

val nat_compare : MlCoq.nat -> MlCoq.nat -> comparison

val nat_compare_alt : MlCoq.nat -> MlCoq.nat -> comparison

val leb : MlCoq.nat -> MlCoq.nat -> bool

