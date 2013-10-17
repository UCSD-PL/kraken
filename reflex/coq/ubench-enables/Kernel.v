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

Definition NB_MSG : nat := 3.

Definition PAYD : vvdesc NB_MSG :=
  mk_vvdesc
  [ ("M1", [])
  ; ("M2", [])
  ; ("M3", [])
  ].

Notation M1 := 0%fin (only parsing).
Notation M2 := 1%fin (only parsing).
Notation M3 := 2%fin (only parsing).

Inductive COMPT' : Type := C1 | C2 | C3.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C1 => mk_compd "C1" "c1" [] (mk_vdesc [])
  | C2 => mk_compd "C2" "c2" [] (mk_vdesc [])
  | C3 => mk_compd "C3" "c3" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT :=
  mk_vcdesc [Desc _ str_d; Desc _ num_d].

Definition st1 : fin (projT1 KSTD) := None.
Definition st2 : fin (projT1 KSTD) := Some None.

Definition IENVD : vcdesc COMPT :=
  mk_vcdesc [Comp _ C1].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  spawn _ IENVD C1 tt None (Logic.eq_refl _).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | M1, C1 =>
    let e := mk_vcdesc [Comp _ C1] in
    [[ e :
         (spawn _ e C2 tt 0%fin (eq_refl _))
    ]]
  | M3, C2 =>
    [[ mk_vcdesc [] :
         (send ccomp M2 tt)
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
