Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexVec.
Require Import ReflexHVec.
Require Import ReflexFin.
Require Import ReflexIO.
Require Import ReflexFrontend.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 2.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("A", [])
  ; ("B", [])
  ].

Notation MA := 0%fin (only parsing).
Notation MB := 1%fin (only parsing).

Inductive COMPT' : Type :=
| C1
| C2
.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C1 => mk_compd "C1" "comp1.py" [] (mk_vdesc [])
  | C2 => mk_compd "C2" "comp2.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [Desc _ str_d; Desc _ str_d].
Definition v_c1 : fin (projT1 KSTD) := 0%fin.
Definition v_c2 : fin (projT1 KSTD) := 1%fin.

Definition IENVD : vcdesc COMPT := mk_vcdesc [Comp _ C1; Comp _ C2].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  seq
    (spawn _ IENVD C1 tt 0%fin (Logic.eq_refl _))
    (spawn _ IENVD C2 tt 1%fin (Logic.eq_refl _))
.

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | MA, _ =>
    let envd := mk_vcdesc [Comp _ C1; Comp _ C2] in
    [[ envd :
         seq
           (spawn _ envd C1 tt 0%fin (Logic.eq_refl _))
           (spawn _ envd C2 tt 1%fin (Logic.eq_refl _))
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
