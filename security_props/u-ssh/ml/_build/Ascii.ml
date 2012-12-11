open BinNat
open BinPos
open Nnat

(** val ascii_rect :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    MlCoq.ascii -> 'a1 **)

let ascii_rect f = function
| MlCoq.Ascii (x, x0, x1, x2, x3, x4, x5, x6) -> f x x0 x1 x2 x3 x4 x5 x6

(** val ascii_rec :
    (bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> 'a1) ->
    MlCoq.ascii -> 'a1 **)

let ascii_rec f = function
| MlCoq.Ascii (x, x0, x1, x2, x3, x4, x5, x6) -> f x x0 x1 x2 x3 x4 x5 x6

(** val zero : MlCoq.ascii **)

let zero =
  MlCoq.Ascii (false, false, false, false, false, false, false, false)

(** val one : MlCoq.ascii **)

let one =
  MlCoq.Ascii (true, false, false, false, false, false, false, false)

(** val shift : bool -> MlCoq.ascii -> MlCoq.ascii **)

let shift c = function
| MlCoq.Ascii (a1, a2, a3, a4, a5, a6, a7, a8) ->
  MlCoq.Ascii (c, a1, a2, a3, a4, a5, a6, a7)

(** val ascii_of_pos : positive -> MlCoq.ascii **)

let ascii_of_pos =
  let rec loop n p =
    match n with
    | MlCoq.O -> zero
    | MlCoq.S n' ->
      (match p with
       | Coq_xI p' -> shift true (loop n' p')
       | Coq_xO p' -> shift false (loop n' p')
       | Coq_xH -> one)
  in loop (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S (MlCoq.S
       (MlCoq.S MlCoq.O))))))))

(** val ascii_of_N : coq_N -> MlCoq.ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : MlCoq.nat -> MlCoq.ascii **)

let ascii_of_nat a =
  ascii_of_N (coq_N_of_nat a)

(** val coq_N_of_digits : bool list -> coq_N **)

let rec coq_N_of_digits = function
| [] -> N0
| b::l' ->
  coq_Nplus (if b then Npos Coq_xH else N0)
    (coq_Nmult (Npos (Coq_xO Coq_xH)) (coq_N_of_digits l'))

(** val coq_N_of_ascii : MlCoq.ascii -> coq_N **)

let coq_N_of_ascii = function
| MlCoq.Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  coq_N_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[]))))))))

(** val nat_of_ascii : MlCoq.ascii -> MlCoq.nat **)

let nat_of_ascii a =
  nat_of_N (coq_N_of_ascii a)

(** val coq_Space : MlCoq.ascii **)

let coq_Space =
  MlCoq.Ascii (false, false, false, false, false, true, false, false)

(** val coq_DoubleQuote : MlCoq.ascii **)

let coq_DoubleQuote =
  MlCoq.Ascii (false, true, false, false, false, true, false, false)

(** val coq_Beep : MlCoq.ascii **)

let coq_Beep =
  MlCoq.Ascii (true, true, true, false, false, false, false, false)

