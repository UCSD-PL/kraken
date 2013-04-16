Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexVec.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("M", [str_d])
  ].

Notation M := (None) (only parsing).

Inductive COMPT' : Type := Echo.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Echo => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [].

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Echo
  ].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  [fun s => spawn IENVD _ Echo tt None (Logic.eq_refl _)
  ].

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun m cc =>
     let (_, cf, _) := cc in
    match m as _m return forall (EQ : _m = m), _ with
    | Build_msg None p => fun EQ =>
      let envd := existT _ 0 tt in
      existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc _ d) envd (
        let (msg, _) := p in fun st0 =>
        [ fun s => sendall envd _
                           (Build_comp_pat COMPT' COMPS Echo (Some cf) tt)
                           None (mvar EQ None, tt)
        ]
      )
    | Build_msg (Some bad) _ =>
      match bad with end
    end (Logic.eq_refl m).

End Spec.

Module Main := MkMain(Spec).
Import Main.
