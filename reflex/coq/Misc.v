Require Import List.
Require Import Ascii.
Require Import ReflexBase.
Require Import Reflex.

Definition dom' (d:ascii) (s:str) :=
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

Definition dom (d:str) :=
  match d with
  | nil    => dom' "/"
  | a :: _ => dom' a
  end.

Fixpoint str_prefix (s1 s2:str) :=
  match s1 with
  | nil => TRUE
  | a1::s1' =>
    match s2 with
    | nil => FALSE
    | a2::s2' =>
      match Ascii.ascii_dec a1 a2 with
      | left _ => str_prefix s1' s2'
      | right _ => FALSE
      end
    end
  end.