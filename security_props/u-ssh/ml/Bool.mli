type __ = Obj.t

val eqb : bool -> bool -> bool

val ifb : bool -> bool -> bool -> bool

val orb_true_elim : bool -> bool -> bool

val andb_false_elim : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val reflect_rect : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val reflect_rec : (__ -> 'a1) -> (__ -> 'a1) -> bool -> reflect -> 'a1

val iff_reflect : bool -> reflect

val reflect_dec : bool -> reflect -> bool

