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
    | Some impossibru => fun _ =>
      match impossibru with end
    end (pay _ _ m)
  )
.

Definition main := mk_main (Build_spec NB_MSG PDV HANDLERS).

(*
Axiom c : fd.

Print kstate_run_prog. Check main.
Eval compute in (msg NB_MSG PDV).
Print msg.

Require Import Ynot.

Definition tr0 := [@nil (KAction NB_MSG PDV)]%inhabited.
Definition ks0 := {|components := c :: nil; ktr := tr0|}.
Definition m := (Build_msg NB_MSG PDV None (str_of_string "Hello", tt)).

Eval compute in (
  kstate_run_prog
    NB_MSG
    PDV
    c
    m
    ks0
    (HANDLERS m)
).
*)