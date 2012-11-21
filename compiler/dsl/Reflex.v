Require Import List.
Require Import Ascii.

(* syntax *)

Inductive type_t : Set :=
| num_t : type_t
| str_t : type_t
.

Definition payload_t : Set :=
  list type_t.

Definition msg_spec : Set :=
  list payload_t.

(* semantics *)

(* follow ascii design, little endian *)
Inductive Num : Set :=
| num : ascii -> ascii -> Num.

Axiom nat_of_Num : Num -> nat.

Definition Str : Set :=
  list ascii.

Definition TypeD (t : type_t) : Set :=
  match t with
  | num_t => Num
  | str_t => Str
  end.

Fixpoint PayloadD (p : payload_t) : Set :=
  match p with
  | nil => unit
  | t :: ts => TypeD t * PayloadD ts
  end%type.

Definition PayloadD' (p : option payload_t) : Set :=
  match p with
  | None => False
  | Some p' => PayloadD p'
  end.

Record Msg (ms : msg_spec) : Set :=
  { tag : Num
  ; pay : PayloadD' (List.nth_error ms (nat_of_Num tag))
  }.