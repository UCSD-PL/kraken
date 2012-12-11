type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

(** val ifb : bool -> bool -> bool -> bool **)

let ifb b1 b2 b3 =
  if b1 then b2 else b3

(** val orb_true_elim : bool -> bool -> bool **)

let orb_true_elim b1 b2 =
  if b1 then true else false

(** val andb_false_elim : bool -> bool -> bool **)

let andb_false_elim b1 b2 =
  if b1 then false else true

type reflect =
| ReflectT
| ReflectF

(** val reflect_rect :
    (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rect f f0 b = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val reflect_rec :
    (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1 **)

let reflect_rec f f0 b = function
| ReflectT -> f __
| ReflectF -> f0 __

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

(** val reflect_dec : bool -> reflect -> bool **)

let reflect_dec b = function
| ReflectT -> true
| ReflectF -> false

