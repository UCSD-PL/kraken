type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type dynamic =
  __
  (* singleton inductive, whose constructor was Dyn *)

(** val dynamic_rect : (__ -> __ -> 'a1) -> dynamic -> 'a1 **)

let dynamic_rect f d =
  f __ d

(** val dynamic_rec : (__ -> __ -> 'a1) -> dynamic -> 'a1 **)

let dynamic_rec f d =
  f __ d

