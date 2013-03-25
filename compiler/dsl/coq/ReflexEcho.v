Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
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

Definition INIT : init_prog PAYD COMPT KSTD (init_msg PAYD) IENVD :=
  [fun s => Spawn _ _ _ _ IENVD Echo None (Logic.eq_refl _)
  ].


Definition HANDLERS : handlers PAYD COMPT KSTD :=
  fun (m : msg PAYD) cfd =>
    match m as _m return forall (EQ : _m = m), _ with
    | Build_msg None p => fun EQ =>
      let envd := existT _ 0 tt in
      existT (fun d => hdlr_prog PAYD COMPT KSTD _ d) envd (
        let (msg, _) := p in fun st0 =>
        [ fun s => Send _ _ _ _ _ (CFd PAYD _ _ _) None (mvar EQ None, tt) ]
      )
    | Build_msg (Some bad) _ =>
      match bad with end
    end (Logic.eq_refl m).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS INIT HANDLERS).
