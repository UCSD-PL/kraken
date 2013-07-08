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
  [ ("M", [fd_d])
  ].

Notation M := 0%fin (only parsing).

Inductive COMPT' : Type := Echo.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Echo => mk_compd "Echo" "test/fd-unique/fd-unique.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [].

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Echo].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq (spawn _ IENVD Echo tt 0%fin (Logic.eq_refl _))
      (send (i_envvar IENVD 0%fin) M (Term _ _ _ (CompFd _ IENVD Echo (Var _ IENVD 0%fin)), tt)).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | None, _ =>
    [[ mk_vcdesc [] :
       send ccomp None (mvar None None, tt) ]]
  | Some bad, _ =>
    match bad with end
  end.
Close Scope hdlr.

End Spec.

Module Main := MkMain(Spec).
Import Main.