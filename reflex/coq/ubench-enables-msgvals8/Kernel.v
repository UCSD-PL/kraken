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
  [
    ("M1", [num_d; str_d; num_d; str_d]);
    ("M2", [str_d; num_d]) 
  ].

Notation M1 := 0%fin (only parsing).
Notation M2 := 1%fin (only parsing).

Inductive COMPT' : Type := C.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C => mk_compd "C" "" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT :=
  mk_vcdesc [].

Definition IENVD : vcdesc COMPT := mk_vcdesc [Comp _ C].
Notation v_env_c := 0%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
   spawn _ IENVD C tt v_env_c (Logic.eq_refl _).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | M1, C =>
    [[ mk_vcdesc [] :
       send ccomp M2 (mvar M1 1%fin, (mvar M1 2%fin, tt))
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
