open BinInt
open BinPos
open Datatypes
open Ring_theory
open Specif
open ZArith_dec
open Zbool

type coq_Q = { coq_Qnum : coq_Z; coq_Qden : positive }

(** val coq_Q_rect : (coq_Z -> positive -> 'a1) -> coq_Q -> 'a1 **)

let coq_Q_rect f q =
  let { coq_Qnum = x; coq_Qden = x0 } = q in f x x0

(** val coq_Q_rec : (coq_Z -> positive -> 'a1) -> coq_Q -> 'a1 **)

let coq_Q_rec f q =
  let { coq_Qnum = x; coq_Qden = x0 } = q in f x x0

(** val coq_Qnum : coq_Q -> coq_Z **)

let coq_Qnum x = x.coq_Qnum

(** val coq_Qden : coq_Q -> positive **)

let coq_Qden x = x.coq_Qden

(** val inject_Z : coq_Z -> coq_Q **)

let inject_Z x =
  { coq_Qnum = x; coq_Qden = Coq_xH }

(** val coq_Qcompare : coq_Q -> coq_Q -> comparison **)

let coq_Qcompare p q =
  coq_Zcompare (coq_Zmult p.coq_Qnum (Zpos q.coq_Qden))
    (coq_Zmult q.coq_Qnum (Zpos p.coq_Qden))

(** val coq_Qeq_dec : coq_Q -> coq_Q -> bool **)

let coq_Qeq_dec x y =
  coq_Z_eq_dec (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
    (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))

(** val coq_Qeq_bool : coq_Q -> coq_Q -> bool **)

let coq_Qeq_bool x y =
  coq_Zeq_bool (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
    (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))

(** val coq_Qle_bool : coq_Q -> coq_Q -> bool **)

let coq_Qle_bool x y =
  coq_Zle_bool (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
    (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))

(** val coq_Qplus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qplus x y =
  { coq_Qnum =
    (coq_Zplus (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
      (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))); coq_Qden =
    (coq_Pmult x.coq_Qden y.coq_Qden) }

(** val coq_Qmult : coq_Q -> coq_Q -> coq_Q **)

let coq_Qmult x y =
  { coq_Qnum = (coq_Zmult x.coq_Qnum y.coq_Qnum); coq_Qden =
    (coq_Pmult x.coq_Qden y.coq_Qden) }

(** val coq_Qopp : coq_Q -> coq_Q **)

let coq_Qopp x =
  { coq_Qnum = (coq_Zopp x.coq_Qnum); coq_Qden = x.coq_Qden }

(** val coq_Qminus : coq_Q -> coq_Q -> coq_Q **)

let coq_Qminus x y =
  coq_Qplus x (coq_Qopp y)

(** val coq_Qinv : coq_Q -> coq_Q **)

let coq_Qinv x =
  match x.coq_Qnum with
  | Z0 -> { coq_Qnum = Z0; coq_Qden = Coq_xH }
  | Zpos p -> { coq_Qnum = (Zpos x.coq_Qden); coq_Qden = p }
  | Zneg p -> { coq_Qnum = (Zneg x.coq_Qden); coq_Qden = p }

(** val coq_Qdiv : coq_Q -> coq_Q -> coq_Q **)

let coq_Qdiv x y =
  coq_Qmult x (coq_Qinv y)

(** val coq_Q_dec : coq_Q -> coq_Q -> bool sumor **)

let coq_Q_dec x y =
  coq_Z_dec' (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
    (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))

(** val coq_Qlt_le_dec : coq_Q -> coq_Q -> bool **)

let coq_Qlt_le_dec x y =
  coq_Z_lt_le_dec (coq_Zmult x.coq_Qnum (Zpos y.coq_Qden))
    (coq_Zmult y.coq_Qnum (Zpos x.coq_Qden))

(** val coq_Qpower_positive : coq_Q -> positive -> coq_Q **)

let coq_Qpower_positive q p =
  pow_pos coq_Qmult q p

(** val coq_Qpower : coq_Q -> coq_Z -> coq_Q **)

let coq_Qpower q = function
| Z0 -> { coq_Qnum = (Zpos Coq_xH); coq_Qden = Coq_xH }
| Zpos p -> coq_Qpower_positive q p
| Zneg p -> coq_Qinv (coq_Qpower_positive q p)

