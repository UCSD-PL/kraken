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
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_Zdivide_dec : coq_Z -> coq_Z -> bool **)

let coq_Zdivide_dec a b =
  match coq_Ztrichotomy_inf a Z0 with
  | Coq_inleft x ->
    if x
    then coq_Z_eq_dec (coq_Zmod b (coq_Zopp a)) Z0
    else coq_Z_eq_dec b Z0
  | Coq_inright -> coq_Z_eq_dec (coq_Zmod b a) Z0

(** val coq_Zis_gcd_rect :
    coq_Z -> coq_Z -> coq_Z -> (__ -> __ -> __ -> 'a1) -> 'a1 **)

let coq_Zis_gcd_rect a b d f =
  f __ __ __

(** val coq_Zis_gcd_rec :
    coq_Z -> coq_Z -> coq_Z -> (__ -> __ -> __ -> 'a1) -> 'a1 **)

let coq_Zis_gcd_rec a b d f =
  f __ __ __

type coq_Euclid =
| Euclid_intro of coq_Z * coq_Z * coq_Z

(** val coq_Euclid_rect :
    coq_Z -> coq_Z -> (coq_Z -> coq_Z -> coq_Z -> __ -> __ -> 'a1) ->
    coq_Euclid -> 'a1 **)

let coq_Euclid_rect a b f = function
| Euclid_intro (x, x0, x1) -> f x x0 x1 __ __

(** val coq_Euclid_rec :
    coq_Z -> coq_Z -> (coq_Z -> coq_Z -> coq_Z -> __ -> __ -> 'a1) ->
    coq_Euclid -> 'a1 **)

let coq_Euclid_rec a b f = function
| Euclid_intro (x, x0, x1) -> f x x0 x1 __ __

(** val euclid_rec :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z ->
    coq_Euclid **)

let euclid_rec a b v3 u1 u2 u3 v1 v2 =
  coq_Zlt_0_rec (fun x h _ _ u4 u5 u6 v4 v5 _ _ _ ->
    if coq_Z_zerop x
    then Euclid_intro (u4, u5, u6)
    else let q = coq_Zdiv u6 x in
         h (coq_Zminus u6 (coq_Zmult q x)) __ __ v4 v5 x
           (coq_Zminus u4 (coq_Zmult q v4)) (coq_Zminus u5 (coq_Zmult q v5))
           __ __ __) v3 __ u1 u2 u3 v1 v2 __ __ __

(** val euclid : coq_Z -> coq_Z -> coq_Euclid **)

let euclid a b =
  if coq_Z_le_gt_dec Z0 b
  then euclid_rec a b b (Zpos Coq_xH) Z0 a Z0 (Zpos Coq_xH)
  else euclid_rec a b (coq_Zopp b) (Zpos Coq_xH) Z0 a Z0 (Zneg Coq_xH)

(** val prime_rect : coq_Z -> (__ -> __ -> 'a1) -> 'a1 **)

let prime_rect p f =
  f __ __

(** val prime_rec : coq_Z -> (__ -> __ -> 'a1) -> 'a1 **)

let prime_rec p f =
  f __ __

(** val coq_Pgcdn : MlCoq.nat -> positive -> positive -> positive **)

let rec coq_Pgcdn n a b =
  match n with
  | MlCoq.O -> Coq_xH
  | MlCoq.S n0 ->
    (match a with
     | Coq_xI a' ->
       (match b with
        | Coq_xI b' ->
          (match coq_Pcompare a' b' Eq with
           | Eq -> a
           | Lt -> coq_Pgcdn n0 (coq_Pminus b' a') a
           | Gt -> coq_Pgcdn n0 (coq_Pminus a' b') b)
        | Coq_xO b0 -> coq_Pgcdn n0 a b0
        | Coq_xH -> Coq_xH)
     | Coq_xO a0 ->
       (match b with
        | Coq_xI p -> coq_Pgcdn n0 a0 b
        | Coq_xO b0 -> Coq_xO (coq_Pgcdn n0 a0 b0)
        | Coq_xH -> Coq_xH)
     | Coq_xH -> Coq_xH)

(** val coq_Pgcd : positive -> positive -> positive **)

let coq_Pgcd a b =
  coq_Pgcdn (plus (coq_Psize a) (coq_Psize b)) a b

(** val coq_Zgcd : coq_Z -> coq_Z -> coq_Z **)

let coq_Zgcd a b =
  match a with
  | Z0 -> coq_Zabs b
  | Zpos a0 ->
    (match b with
     | Z0 -> coq_Zabs a
     | Zpos b0 -> Zpos (coq_Pgcd a0 b0)
     | Zneg b0 -> Zpos (coq_Pgcd a0 b0))
  | Zneg a0 ->
    (match b with
     | Z0 -> coq_Zabs a
     | Zpos b0 -> Zpos (coq_Pgcd a0 b0)
     | Zneg b0 -> Zpos (coq_Pgcd a0 b0))

(** val coq_Zgcd_spec : coq_Z -> coq_Z -> coq_Z **)

let coq_Zgcd_spec x y =
  coq_Zgcd x y

(** val rel_prime_dec : coq_Z -> coq_Z -> bool **)

let rel_prime_dec a b =
  coq_Z_eq_dec (coq_Zgcd a b) (Zpos Coq_xH)

(** val prime_dec_aux : coq_Z -> coq_Z -> bool **)

let prime_dec_aux p m =
  if coq_Z_lt_dec (Zpos Coq_xH) m
  then natlike_rec true (fun x _ iH ->
         if iH
         then let s = rel_prime_dec x p in
              if s
              then true
              else if coq_Z_lt_dec (Zpos Coq_xH) x then false else true
         else false) m
  else true

(** val prime_dec : coq_Z -> bool **)

let prime_dec p =
  if coq_Z_lt_dec (Zpos Coq_xH) p then prime_dec_aux p p else false

(** val coq_Pggcdn :
    MlCoq.nat -> positive -> positive -> (positive, (positive, positive)
    prod) prod **)

let rec coq_Pggcdn n a b =
  match n with
  | MlCoq.O -> Coq_pair (Coq_xH, (Coq_pair (a, b)))
  | MlCoq.S n0 ->
    (match a with
     | Coq_xI a' ->
       (match b with
        | Coq_xI b' ->
          (match coq_Pcompare a' b' Eq with
           | Eq -> Coq_pair (a, (Coq_pair (Coq_xH, Coq_xH)))
           | Lt ->
             let Coq_pair (g, p) = coq_Pggcdn n0 (coq_Pminus b' a') a in
             let Coq_pair (ba, aa) = p in
             Coq_pair (g, (Coq_pair (aa, (coq_Pplus aa (Coq_xO ba)))))
           | Gt ->
             let Coq_pair (g, p) = coq_Pggcdn n0 (coq_Pminus a' b') b in
             let Coq_pair (ab, bb) = p in
             Coq_pair (g, (Coq_pair ((coq_Pplus bb (Coq_xO ab)), bb))))
        | Coq_xO b0 ->
          let Coq_pair (g, p) = coq_Pggcdn n0 a b0 in
          let Coq_pair (aa, bb) = p in
          Coq_pair (g, (Coq_pair (aa, (Coq_xO bb))))
        | Coq_xH -> Coq_pair (Coq_xH, (Coq_pair (a, Coq_xH))))
     | Coq_xO a0 ->
       (match b with
        | Coq_xI p ->
          let Coq_pair (g, p0) = coq_Pggcdn n0 a0 b in
          let Coq_pair (aa, bb) = p0 in
          Coq_pair (g, (Coq_pair ((Coq_xO aa), bb)))
        | Coq_xO b0 ->
          let Coq_pair (g, p) = coq_Pggcdn n0 a0 b0 in
          Coq_pair ((Coq_xO g), p)
        | Coq_xH -> Coq_pair (Coq_xH, (Coq_pair (a, Coq_xH))))
     | Coq_xH -> Coq_pair (Coq_xH, (Coq_pair (Coq_xH, b))))

(** val coq_Pggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod **)

let coq_Pggcd a b =
  coq_Pggcdn (plus (coq_Psize a) (coq_Psize b)) a b

(** val coq_Zggcd : coq_Z -> coq_Z -> (coq_Z, (coq_Z, coq_Z) prod) prod **)

let coq_Zggcd a b =
  match a with
  | Z0 -> Coq_pair ((coq_Zabs b), (Coq_pair (Z0, (coq_Zsgn b))))
  | Zpos a0 ->
    (match b with
     | Z0 -> Coq_pair ((coq_Zabs a), (Coq_pair ((coq_Zsgn a), Z0)))
     | Zpos b0 ->
       let Coq_pair (g, p) = coq_Pggcd a0 b0 in
       let Coq_pair (aa, bb) = p in
       Coq_pair ((Zpos g), (Coq_pair ((Zpos aa), (Zpos bb))))
     | Zneg b0 ->
       let Coq_pair (g, p) = coq_Pggcd a0 b0 in
       let Coq_pair (aa, bb) = p in
       Coq_pair ((Zpos g), (Coq_pair ((Zpos aa), (Zneg bb)))))
  | Zneg a0 ->
    (match b with
     | Z0 -> Coq_pair ((coq_Zabs a), (Coq_pair ((coq_Zsgn a), Z0)))
     | Zpos b0 ->
       let Coq_pair (g, p) = coq_Pggcd a0 b0 in
       let Coq_pair (aa, bb) = p in
       Coq_pair ((Zpos g), (Coq_pair ((Zneg aa), (Zpos bb))))
     | Zneg b0 ->
       let Coq_pair (g, p) = coq_Pggcd a0 b0 in
       let Coq_pair (aa, bb) = p in
       Coq_pair ((Zpos g), (Coq_pair ((Zneg aa), (Zneg bb)))))

