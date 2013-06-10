Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexIO.
Require Import ReflexVec.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [ ("M", [str_d])
  ].

Notation M := 0%fin (only parsing).

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
  seq (spawn IENVD _ Echo tt None (Logic.eq_refl _))
  nop.

Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun m cc =>
  let (_, cf, _) := cc in
  match m as _m return forall (EQ : _m = m), _ with
  | {| tag := t; pay := p |} =>
  match t as _t return
    forall _p, Build_msg PAYD _t _p = m -> _
  with
  | None => fun p EQ =>
    let envd := existT _ 0 tt in
    existT (fun d => hdlr_prog PAYD COMPT COMPS KSTD cc _ d) envd (
      seq (send envd _ _ ccomp None (mvar EQ None, tt))
      nop
    )
  | Some bad =>
    match bad with end
  end p
  end (Logic.eq_refl m).

End Spec.

Module Main := MkMain(Spec).
Import Main.
