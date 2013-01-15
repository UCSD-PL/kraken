Require Import List.

Section DepList.

Variable T : Type.
Variable denote : T -> Type.

Inductive dlist : list T -> Type :=
| dnil :
  dlist nil
| dcons :
  forall (t : T) (ts : list T), denote t -> dlist ts -> dlist (t :: ts)
.

Implicit Arguments dcons [t ts].

Fixpoint tgeti (ts : list T) (i : nat) : option T :=
  match ts with
  | nil => None
  | t :: ts' =>
    match i with
    | O => Some t
    | S i' => tgeti ts' i'
    end
  end.

Fixpoint geti {ts : list T} (vs : dlist ts) (i : nat)
  : match tgeti ts i with Some t => denote t | None => unit end :=
  match vs as vs' in dlist ts' return
    match tgeti ts' i with
    | Some t => denote t
    | None => unit
    end
  with
  | dnil => tt
  | dcons t ts' v vs' =>
    match i as i' return 
      match tgeti (t :: ts') i' with
      | Some t => denote t
      | None => unit
      end
    with
    | O => v
    | S i' => geti vs' i'
    end
  end.

End DepList.