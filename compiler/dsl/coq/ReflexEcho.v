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

Notation "'M'" := (None) (only parsing).

Definition KSTD : vdesc := mk_vdesc [].

Definition IENVD : vdesc := mk_vdesc
  [ fd_d 
  ].

Inductive COMPT : Type := Echo.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Echo => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition IMSG : msg PAYD := @Build_msg _ PAYD M (str_of_string "", tt).

Definition INIT : init_prog PAYD COMPT COMPS KSTD IMSG IENVD :=
  [fun s => Spawn _ _ COMPS _ _ IENVD Echo tt None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun (m : msg PAYD) cfd =>
    match m as _m return forall (EQ : _m = m), _ with
    | Build_msg None p => fun EQ =>
      let envd := existT _ 0 tt in
      existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD _ d) envd (
        let (msg, _) := p in fun st0 =>
        [ fun s => Send _ _ _ _ _ _ (CFd PAYD _ _ _) None (mvar EQ None, tt) ]
      )
    | Build_msg (Some bad) _ =>
      match bad with end
    end (Logic.eq_refl m).

Definition main := mk_main (Build_spec NB_MSG PAYD IENVD KSTD COMPT COMPTDEC COMPS IMSG INIT HANDLERS).
