open BinInt
open BinPos
open Peano

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val coq_ZL4_inf : positive -> MlCoq.nat **)

let rec coq_ZL4_inf = function
| Coq_xI p0 -> let h = coq_ZL4_inf p0 in plus (MlCoq.S h) (MlCoq.S h)
| Coq_xO p0 -> let h1 = coq_ZL4_inf p0 in plus h1 (MlCoq.S h1)
| Coq_xH -> MlCoq.O

(** val coq_Z_of_nat_complete_inf : coq_Z -> MlCoq.nat **)

let coq_Z_of_nat_complete_inf = function
| Z0 -> MlCoq.O
| Zpos p -> let h0 = coq_ZL4_inf p in MlCoq.S h0
| Zneg p -> assert false (* absurd case *)

(** val coq_Z_of_nat_set : (MlCoq.nat -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_of_nat_set h x =
  let h1 = coq_Z_of_nat_complete_inf x in h h1

(** val natlike_rec : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1 **)

let natlike_rec h h0 x =
  coq_Z_of_nat_set (fun n ->
    let rec f = function
    | MlCoq.O -> h
    | MlCoq.S n1 -> h0 (coq_Z_of_nat n1) __ (f n1)
    in f n) x

(** val natlike_rec2 : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1 **)

let natlike_rec2 x x0 z =
  let rec f x1 =
    let x2 = fun y -> f y in
    (fun _ ->
    match x1 with
    | Z0 -> x
    | Zpos p -> x0 (coq_Zpred (Zpos p)) __ (x2 (coq_Zpred (Zpos p)) __)
    | Zneg p -> assert false (* absurd case *))
  in f z __

(** val natlike_rec3 : 'a1 -> (coq_Z -> __ -> 'a1 -> 'a1) -> coq_Z -> 'a1 **)

let natlike_rec3 x x0 z =
  let rec f x1 =
    let x2 = fun y -> f y in
    (fun _ ->
    match x1 with
    | Z0 -> x
    | Zpos p -> x0 (Zpos p) __ (x2 (coq_Zpred (Zpos p)) __)
    | Zneg p -> assert false (* absurd case *))
  in f z __

(** val coq_Zlt_0_rec :
    (coq_Z -> (coq_Z -> __ -> 'a1) -> __ -> 'a1) -> coq_Z -> 'a1 **)

let coq_Zlt_0_rec x x0 =
  let rec f x1 =
    let x2 = fun y -> f y in
    (fun _ ->
    match x1 with
    | Z0 -> x Z0 (fun y _ -> assert false (* absurd case *)) __
    | Zpos p -> let h0 = fun y -> x2 y __ in x (Zpos p) (fun y _ -> h0 y) __
    | Zneg p -> assert false (* absurd case *))
  in f x0 __

(** val coq_Z_lt_rec :
    (coq_Z -> (coq_Z -> __ -> 'a1) -> 'a1) -> coq_Z -> 'a1 **)

let coq_Z_lt_rec x x0 =
  coq_Zlt_0_rec (fun x1 x2 _ -> x x1 x2) x0

(** val coq_Zlt_lower_bound_rec :
    coq_Z -> (coq_Z -> (coq_Z -> __ -> 'a1) -> __ -> 'a1) -> coq_Z -> 'a1 **)

let coq_Zlt_lower_bound_rec z x x0 =
  coq_Zlt_0_rec (fun x1 hlt_x0 _ ->
    x (coq_Zplus x1 z) (fun y _ -> hlt_x0 (coq_Zminus y z) __) __)
    (coq_Zminus x0 z)

