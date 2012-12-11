open BinNat
open BinPos
open Nnat

val ascii_rect :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  MlCoq.ascii -> 'a1

val ascii_rec :
  (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
  MlCoq.ascii -> 'a1

val zero : MlCoq.ascii

val one : MlCoq.ascii

val shift : bool -> MlCoq.ascii -> MlCoq.ascii

val ascii_of_pos : positive -> MlCoq.ascii

val ascii_of_N : coq_N -> MlCoq.ascii

val ascii_of_nat : MlCoq.nat -> MlCoq.ascii

val coq_N_of_digits : bool list -> coq_N

val coq_N_of_ascii : MlCoq.ascii -> coq_N

val nat_of_ascii : MlCoq.ascii -> MlCoq.nat

val coq_Space : MlCoq.ascii

val coq_DoubleQuote : MlCoq.ascii

val coq_Beep : MlCoq.ascii

