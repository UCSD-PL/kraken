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

Definition NB_CFGD := 1.

Definition CFGD := mk_vvdesc
  [("Echo", [str_d])
  ].

Notation t_cfg_echo := (None) (only parsing).

Definition INIT : init_prog PAYD COMPT KSTD CFGD (init_msg PAYD) IENVD :=
  [fun s => Spawn _ _ _ CFGD _ IENVD Echo t_cfg_echo
                  (str_of_string "Echo",tt) None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT KSTD CFGD :=
  fun (m : msg PAYD) cfd =>
    match m as _m return forall (EQ : _m = m), _ with
    | Build_msg None p => fun EQ =>
      let envd := existT _ 0 tt in
      existT (fun d => hdlr_prog PAYD COMPT KSTD CFGD _ d) envd (
        let (msg, _) := p in fun st0 =>
        [ fun s => Send _ _ _ _ _ _ (CFd PAYD _ _ _) None (mvar EQ None, tt) ]
      )
    | Build_msg (Some bad) _ =>
      match bad with end
    end (Logic.eq_refl m).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPS NB_CFGD CFGD INIT HANDLERS).
