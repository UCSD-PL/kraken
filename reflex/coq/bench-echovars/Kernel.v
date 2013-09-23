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

Inductive COMPT' : Type := Echo1 | Echo2.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | Echo1 => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  | Echo2 => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [Desc _ num_d; Desc _ num_d].

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ Echo1;
    Comp _ Echo2
  ].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq (spawn _ IENVD Echo1 tt None (Logic.eq_refl _))
  (seq (spawn _ IENVD Echo2 tt (Some None) (Logic.eq_refl _))
  nop).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | None, Echo1 =>
    [[ mk_vcdesc [] :
       seq (send ccomp None (mvar None None, tt))
           (stupd _ _ None (nlit (num_of_nat 1)))]]
  | None, Echo2 =>
    [[ mk_vcdesc [] :
       seq (send ccomp None (mvar None None, tt))
           (stupd _ _ (Some None) (nlit (num_of_nat 1)))]]
  | Some bad, _ =>
    match bad with end
  end.
Close Scope hdlr.

End Spec.

Module Main := MkMain(Spec).
Import Main.
