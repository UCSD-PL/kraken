open BinNat
open BinPos
open Datatypes

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module RingSyntax = 
 struct 
  
 end

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| Coq_xI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| Coq_xO i0 -> let p = pow_pos rmul x i0 in rmul p p
| Coq_xH -> x

(** val pow_N : 'a1 -> ('a1 -> 'a1 -> 'a1) -> 'a1 -> coq_N -> 'a1 **)

let pow_N rI rmul x = function
| N0 -> rI
| Npos p0 -> pow_pos rmul x p0

(** val id_phi_N : coq_N -> coq_N **)

let id_phi_N x =
  x

(** val semi_ring_theory_rect :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> (__ -> __ ->
    __ -> __ -> __ -> __ -> __ -> __ -> 'a2) -> 'a2 **)

let semi_ring_theory_rect rO rI radd rmul f =
  f __ __ __ __ __ __ __ __

(** val semi_ring_theory_rec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> (__ -> __ ->
    __ -> __ -> __ -> __ -> __ -> __ -> 'a2) -> 'a2 **)

let semi_ring_theory_rec rO rI radd rmul f =
  f __ __ __ __ __ __ __ __

(** val almost_ring_theory_rect :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> __
    -> __ -> __ -> __ -> 'a2) -> 'a2 **)

let almost_ring_theory_rect rO rI radd rmul rsub ropp f =
  f __ __ __ __ __ __ __ __ __ __ __

(** val almost_ring_theory_rec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> __
    -> __ -> __ -> __ -> 'a2) -> 'a2 **)

let almost_ring_theory_rec rO rI radd rmul rsub ropp f =
  f __ __ __ __ __ __ __ __ __ __ __

(** val ring_theory_rect :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a2) -> 'a2 **)

let ring_theory_rect rO rI radd rmul rsub ropp f =
  f __ __ __ __ __ __ __ __ __

(** val ring_theory_rec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> __
    -> __ -> 'a2) -> 'a2 **)

let ring_theory_rec rO rI radd rmul rsub ropp f =
  f __ __ __ __ __ __ __ __ __

(** val sring_eq_ext_rect :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> (__ -> __ -> 'a2) -> 'a2 **)

let sring_eq_ext_rect radd rmul f =
  f __ __

(** val sring_eq_ext_rec :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> (__ -> __ -> 'a2) -> 'a2 **)

let sring_eq_ext_rec radd rmul f =
  f __ __

(** val ring_eq_ext_rect :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> (__ -> __
    -> __ -> 'a2) -> 'a2 **)

let ring_eq_ext_rect radd rmul ropp f =
  f __ __ __

(** val ring_eq_ext_rec :
    ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1) -> (__ -> __
    -> __ -> 'a2) -> 'a2 **)

let ring_eq_ext_rec radd rmul ropp f =
  f __ __ __

(** val semi_morph_rect :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> 'a2 ->
    ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> bool) ->
    ('a2 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> 'a3) -> 'a3 **)

let semi_morph_rect rO rI radd rmul cO cI cadd cmul ceqb phi f =
  f __ __ __ __ __

(** val semi_morph_rec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> 'a2 -> 'a2 ->
    ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> bool) ->
    ('a2 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> 'a3) -> 'a3 **)

let semi_morph_rec rO rI radd rmul cO cI cadd cmul ceqb phi f =
  f __ __ __ __ __

(** val ring_morph_rect :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> 'a2) -> ('a2 ->
    'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2) -> ('a2 -> 'a2 ->
    bool) -> ('a2 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> 'a3)
    -> 'a3 **)

let ring_morph_rect rO rI radd rmul rsub ropp cO cI cadd cmul csub copp ceqb phi f =
  f __ __ __ __ __ __ __

(** val ring_morph_rec :
    'a1 -> 'a1 -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1 -> 'a1) -> ('a1 -> 'a1
    -> 'a1) -> ('a1 -> 'a1) -> 'a2 -> 'a2 -> ('a2 -> 'a2 -> 'a2) -> ('a2 ->
    'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2) -> ('a2 -> 'a2 ->
    bool) -> ('a2 -> 'a1) -> (__ -> __ -> __ -> __ -> __ -> __ -> __ -> 'a3)
    -> 'a3 **)

let ring_morph_rec rO rI radd rmul rsub ropp cO cI cadd cmul csub copp ceqb phi f =
  f __ __ __ __ __ __ __

(** val sign_theory_rect :
    ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 option) -> (__ ->
    'a2) -> 'a2 **)

let sign_theory_rect copp ceqb get_sign f =
  f __

(** val sign_theory_rec :
    ('a1 -> 'a1) -> ('a1 -> 'a1 -> bool) -> ('a1 -> 'a1 option) -> (__ ->
    'a2) -> 'a2 **)

let sign_theory_rec copp ceqb get_sign f =
  f __

(** val get_sign_None : 'a1 -> 'a1 option **)

let get_sign_None c =
  None

(** val div_theory_rect :
    ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2
    -> ('a2, 'a2) prod) -> (__ -> 'a3) -> 'a3 **)

let div_theory_rect cadd cmul phi cdiv f =
  f __

(** val div_theory_rec :
    ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a2 -> 'a2) -> ('a2 -> 'a1) -> ('a2 -> 'a2
    -> ('a2, 'a2) prod) -> (__ -> 'a3) -> 'a3 **)

let div_theory_rec cadd cmul phi cdiv f =
  f __

(** val coq_IDphi : 'a1 -> 'a1 **)

let coq_IDphi x =
  x

(** val power_theory_rect :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> (coq_N -> 'a2) -> ('a1 -> 'a2 -> 'a1) ->
    (__ -> 'a3) -> 'a3 **)

let power_theory_rect rI rmul cp_phi rpow f =
  f __

(** val power_theory_rec :
    'a1 -> ('a1 -> 'a1 -> 'a1) -> (coq_N -> 'a2) -> ('a1 -> 'a2 -> 'a1) ->
    (__ -> 'a3) -> 'a3 **)

let power_theory_rec rI rmul cp_phi rpow f =
  f __

(** val coq_SRopp : 'a1 -> 'a1 **)

let coq_SRopp x =
  x

(** val coq_SRsub : ('a1 -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

let coq_SRsub radd x y =
  radd x (coq_SRopp y)

type ring_kind =
| Abstract
| Computational of (__ -> __ -> bool)
| Morphism of __ * __ * (__ -> __ -> __) * (__ -> __ -> __)
   * (__ -> __ -> __) * (__ -> __) * __ * __ * (__ -> __ -> __)
   * (__ -> __ -> __) * (__ -> __ -> __) * (__ -> __) * (__ -> __ -> bool)
   * (__ -> __)

(** val ring_kind_rect :
    'a1 -> (__ -> __ -> (__ -> __ -> bool) -> __ -> 'a1) -> (__ -> __ -> __
    -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ -> __)
    -> __ -> __ -> __ -> __ -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ ->
    __ -> __) -> (__ -> __) -> (__ -> __ -> bool) -> (__ -> __) -> __ -> 'a1)
    -> ring_kind -> 'a1 **)

let ring_kind_rect f f0 f1 = function
| Abstract -> f
| Computational x -> f0 __ __ x __
| Morphism (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
  f1 __ x x0 x1 x2 x3 x4 __ __ x5 x6 x7 x8 x9 x10 x11 x12 __

(** val ring_kind_rec :
    'a1 -> (__ -> __ -> (__ -> __ -> bool) -> __ -> 'a1) -> (__ -> __ -> __
    -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ -> __)
    -> __ -> __ -> __ -> __ -> (__ -> __ -> __) -> (__ -> __ -> __) -> (__ ->
    __ -> __) -> (__ -> __) -> (__ -> __ -> bool) -> (__ -> __) -> __ -> 'a1)
    -> ring_kind -> 'a1 **)

let ring_kind_rec f f0 f1 = function
| Abstract -> f
| Computational x -> f0 __ __ x __
| Morphism (x, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12) ->
  f1 __ x x0 x1 x2 x3 x4 __ __ x5 x6 x7 x8 x9 x10 x11 x12 __

