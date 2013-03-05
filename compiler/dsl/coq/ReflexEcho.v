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

Definition KST_DESC_SIZE := 0.

(*State is (username, authres)*)
Definition KST_DESC : vdesc' KST_DESC_SIZE := tt.

Definition INIT : @init_prog NB_MSG PAY_DESC _ KST_DESC INIT_ENVD :=
  nil.

Definition HANDLERS : handlers (VVD := PAY_DESC) KST_DESC :=
  (fun m f s =>
    match tag m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag (VVD := PAY_DESC) _tm) -> _
    with
    | None => fun pl =>
       let envd := existT _ 0 tt in
       existT _ envd (
        let (s, _) := pl in
        Send _ _ _
          (HEchan _ _)
          (@MEmsg _ PAY_DESC envd None (SLit _ s, tt))
        :: nil
      )
    | Some bad => fun _ =>
      match bad with end
    end (pay m)
  ).

(*Definition main := mk_main (Build_spec NB_MSG PAY_DESC INIT_ENVD INIT KST_DESC HANDLERS).*)
