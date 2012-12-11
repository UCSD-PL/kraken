type __ = Obj.t

type dynamic =
  __
  (* singleton inductive, whose constructor was Dyn *)

val dynamic_rect : (__ -> __ -> 'a1) -> dynamic -> 'a1

val dynamic_rec : (__ -> __ -> 'a1) -> dynamic -> 'a1

