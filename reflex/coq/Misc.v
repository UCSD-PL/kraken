Require Import List.
Require Import Ascii.
Require Import ReflexBase.
Require Import Reflex.

Definition dom (d:ascii) (s:str) :=
  let fix dom_aux s n res :=
    match s with
    | nil => List.rev res
    | h::s' => if Ascii.ascii_dec h "."
               then match n with
                    | O => List.rev res
                    | S n' => dom_aux s' n' (h::res)
                    end
               else dom_aux s' n (h::res)
    end in
  List.rev (dom_aux (List.rev (fst (splitAt d s))) 1 nil).
