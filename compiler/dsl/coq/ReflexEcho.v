Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.

Definition NB_MSG : nat := 1.

Definition PAY_DESC : vvdesc NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition INIT_ENVD : vdesc := existT _ 0 tt.

Definition INIT : @init_prog NB_MSG PAY_DESC INIT_ENVD :=
  nil.

Definition KST_DESC : vdesc := existT _ 0 tt.

Definition HANDLERS : handlers (VVD := PAY_DESC) (projT2 KST_DESC) :=
  (fun m =>
    match tag m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag (VVD := PAY_DESC) _tm) -> _
    with
    | None => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog (projT2 KST_DESC) d) envd (fun cm cfd s =>
        let (s, _) := pl in
        Send (VVD := PAY_DESC) envd (CFd _) None (SLit _ s, tt)
        :: nil
      )
    | Some bad => fun _ =>
      match bad with end
    end (pay m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAY_DESC INIT_ENVD INIT KST_DESC HANDLERS).
