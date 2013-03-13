Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG :=
  ( existT _ 1 (str_d, tt)
  , tt
  ).

Definition KSTD : vdesc := existT _ 0 tt.

Definition IENVD : vdesc := existT _ 0 tt.

Definition INIT : init_prog PAYD KSTD IENVD :=
  nil.

Definition HANDLERS : handlers PAYD KSTD :=
  (fun m =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with
    | None => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD KSTD d) envd (fun cfd s =>
        let (s, _) := pl in
        (fun st0 =>
           (fun st => Send PAYD envd (CFd _) None (SLit _ s, tt))
           :: nil
        )
      )
    | Some bad => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD INIT HANDLERS).
