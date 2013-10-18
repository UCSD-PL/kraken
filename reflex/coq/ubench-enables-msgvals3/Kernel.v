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

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("M", [num_d; str_d])
  ].

Notation M := 0%fin (only parsing).

Inductive COMPT' : Type := C1 | C2.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C1 => mk_compd "C1" "" [] (mk_vdesc [])
  | C2 => mk_compd "C2" "" [] (mk_vdesc [num_d; str_d])
  end.

Definition KSTD : vcdesc COMPT :=
  mk_vcdesc [].

Definition IENVD : vcdesc COMPT := mk_vcdesc [Comp _ C1].
Notation v_env_c1 := 0%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
   spawn _ IENVD C1 tt v_env_c1 (Logic.eq_refl _).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | M, C1 =>
    let envd := mk_vcdesc [Comp _ C2] in
    [[ envd :
       ite (eq (nlit FALSE) (nlit FALSE))
           (
             nop
           )
           (
             spawn _ envd C2 (mvar M 0%fin, (mvar M 1%fin, tt)) 0%fin (Logic.eq_refl _)
           )
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
