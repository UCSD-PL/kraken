Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.

Definition NB_MSG : nat := 1.

Definition PDV : payload_desc_vec NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition HANDLERS : handler NB_MSG PDV :=
  (fun m =>
    match tag _ _ m as _tm return
      @sdenote _ SDenoted_payload_desc (lkup_tag NB_MSG PDV _tm) -> _
    with
    | None => fun pl =>
      let (s, _) := pl in
         Send _ _ m
           (CurChan _ _ _)
           (MsgExpr _ _ m None (SLit _ _ m s, tt))
      :: nil
    | Some bad => fun _ =>
      match bad with end
    end (pay _ _ m)
  )
.

Definition main := mk_main (Build_spec NB_MSG PDV HANDLERS).
