Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.

Open Scope string_scope.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("M", [str_d])
  ].

Definition KSTD : vdesc := mk_vdesc [].

Definition IENVD : vdesc := mk_vdesc
  [ fd_d 
  ].

Inductive COMPT : Type := Echo.

Definition COMPS (t : COMPT) : comp :=
  match t with
  | Echo => mk_comp "Echo" "test/echo-00/test.py" []
  end.

Definition INIT : init_prog PAYD COMPT KSTD IENVD :=
  [fun s => Spawn _ _ _ IENVD Echo None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT KSTD :=
  (fun m cfd =>
    match tag PAYD m as _tm return
      @sdenote _ SDenoted_vdesc (lkup_tag PAYD _tm) -> _
    with
    | None => fun pl =>
       let envd := existT _ 0 tt in
       existT (fun d => hdlr_prog PAYD COMPT KSTD d) envd (
         let (msg, _) := pl in fun st0 =>
         [ fun s => Send PAYD _ _ _ (CFd _ _) None (SLit _ _ msg, tt)
         ]
       )
    | Some bad => fun _ =>
      match bad with end
    end (pay PAYD m)
  ).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS INIT HANDLERS).
