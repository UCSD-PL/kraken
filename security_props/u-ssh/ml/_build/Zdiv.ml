open BinInt
open BinPos
open Datatypes
open ZArith_dec
open Zbool

(** val coq_Zdiv_eucl_POS : positive -> coq_Z -> (coq_Z, coq_Z) prod **)

let rec coq_Zdiv_eucl_POS a b =
  match a with
  | Coq_xI a' ->
    let Coq_pair (q, r) = coq_Zdiv_eucl_POS a' b in
    let r' = coq_Zplus (coq_Zmult (Zpos (Coq_xO Coq_xH)) r) (Zpos Coq_xH) in
    if coq_Zgt_bool b r'
    then Coq_pair ((coq_Zmult (Zpos (Coq_xO Coq_xH)) q), r')
    else Coq_pair
           ((coq_Zplus (coq_Zmult (Zpos (Coq_xO Coq_xH)) q) (Zpos Coq_xH)),
           (coq_Zminus r' b))
  | Coq_xO a' ->
    let Coq_pair (q, r) = coq_Zdiv_eucl_POS a' b in
    let r' = coq_Zmult (Zpos (Coq_xO Coq_xH)) r in
    if coq_Zgt_bool b r'
    then Coq_pair ((coq_Zmult (Zpos (Coq_xO Coq_xH)) q), r')
    else Coq_pair
           ((coq_Zplus (coq_Zmult (Zpos (Coq_xO Coq_xH)) q) (Zpos Coq_xH)),
           (coq_Zminus r' b))
  | Coq_xH ->
    if coq_Zge_bool b (Zpos (Coq_xO Coq_xH))
    then Coq_pair (Z0, (Zpos Coq_xH))
    else Coq_pair ((Zpos Coq_xH), Z0)

(** val coq_Zdiv_eucl : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod **)

let coq_Zdiv_eucl a b =
  match a with
  | Z0 -> Coq_pair (Z0, Z0)
  | Zpos a' ->
    (match b with
     | Z0 -> Coq_pair (Z0, Z0)
     | Zpos p -> coq_Zdiv_eucl_POS a' b
     | Zneg b' ->
       let Coq_pair (q, r) = coq_Zdiv_eucl_POS a' (Zpos b') in
       (match r with
        | Z0 -> Coq_pair ((coq_Zopp q), Z0)
        | _ ->
          Coq_pair ((coq_Zopp (coq_Zplus q (Zpos Coq_xH))), (coq_Zplus b r))))
  | Zneg a' ->
    (match b with
     | Z0 -> Coq_pair (Z0, Z0)
     | Zpos p ->
       let Coq_pair (q, r) = coq_Zdiv_eucl_POS a' b in
       (match r with
        | Z0 -> Coq_pair ((coq_Zopp q), Z0)
        | _ ->
          Coq_pair ((coq_Zopp (coq_Zplus q (Zpos Coq_xH))), (coq_Zminus b r)))
     | Zneg b' ->
       let Coq_pair (q, r) = coq_Zdiv_eucl_POS a' (Zpos b') in
       Coq_pair (q, (coq_Zopp r)))

(** val coq_Zdiv : coq_Z -> coq_Z -> coq_Z **)

let coq_Zdiv a b =
  let Coq_pair (q, x) = coq_Zdiv_eucl a b in q

(** val coq_Zmod : coq_Z -> coq_Z -> coq_Z **)

let coq_Zmod a b =
  let Coq_pair (x, r) = coq_Zdiv_eucl a b in r

(** val coq_Zdiv_eucl_exist : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod **)

let coq_Zdiv_eucl_exist b a =
  coq_Zdiv_eucl a b

(** val coq_Zmod_POS : positive -> coq_Z -> coq_Z **)

let rec coq_Zmod_POS a b =
  match a with
  | Coq_xI a' ->
    let r = coq_Zmod_POS a' b in
    let r' = coq_Zplus (coq_Zmult (Zpos (Coq_xO Coq_xH)) r) (Zpos Coq_xH) in
    if coq_Zgt_bool b r' then r' else coq_Zminus r' b
  | Coq_xO a' ->
    let r = coq_Zmod_POS a' b in
    let r' = coq_Zmult (Zpos (Coq_xO Coq_xH)) r in
    if coq_Zgt_bool b r' then r' else coq_Zminus r' b
  | Coq_xH ->
    if coq_Zge_bool b (Zpos (Coq_xO Coq_xH)) then Zpos Coq_xH else Z0

(** val coq_Zmod' : coq_Z -> coq_Z -> coq_Z **)

let coq_Zmod' a b =
  match a with
  | Z0 -> Z0
  | Zpos a' ->
    (match b with
     | Z0 -> Z0
     | Zpos p -> coq_Zmod_POS a' b
     | Zneg b' ->
       let r = coq_Zmod_POS a' (Zpos b') in
       (match r with
        | Z0 -> Z0
        | _ -> coq_Zplus b r))
  | Zneg a' ->
    (match b with
     | Z0 -> Z0
     | Zpos p ->
       let r = coq_Zmod_POS a' b in
       (match r with
        | Z0 -> Z0
        | _ -> coq_Zminus b r)
     | Zneg b' -> coq_Zopp (coq_Zmod_POS a' (Zpos b')))

(** val coq_Zdiv_eucl_extended : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod **)

let coq_Zdiv_eucl_extended b a =
  if coq_Z_le_gt_dec Z0 b
  then coq_Zdiv_eucl_exist b a
  else let Coq_pair (x, x0) = coq_Zdiv_eucl_exist (coq_Zopp b) a in
       Coq_pair ((coq_Zopp x), x0)

