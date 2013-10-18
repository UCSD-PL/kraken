Require Import String.

Require Import Reflex.
Require Import ReflexBase.
Require Import ReflexDenoted.
Require Import ReflexFin.
Require Import ReflexFrontend.
Require Import ReflexHVec.
Require Import ReflexIO.
Require Import ReflexVec.

Open Scope string_scope.

Module SystemFeatures <: SystemFeaturesInterface.

Definition NB_MSG : nat := 1.

Definition PAYD : vvdesc NB_MSG := mk_vvdesc
  [
    ("M",   [num_d])
  ].

Inductive COMPT' : Type := C.

Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C => mk_compd
           "C" "" []
           (mk_vdesc [])
  end.

Notation M        := 0%fin (only parsing).

Definition IENVD : vcdesc COMPT := mk_vcdesc
  [ Comp _ C].

Notation v_env_c := 0%fin (only parsing).

Definition KSTD : vcdesc COMPT := mk_vcdesc
  [Desc _ num_d (* attempts *)].

Notation v_st_att     := 0%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Module Spec <: SpecInterface.

Include SystemFeatures.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  spawn _ IENVD C tt v_env_c (Logic.eq_refl _).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match ct as _ct, t as _t return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
     | C, M =>
       [[ mk_vcdesc [] :
          ite (lt (stvar v_st_att) (nlit (num_of_nat 3)))
              (
                seq (send ccomp M (stvar v_st_att, tt))
                    (stupd _ _ v_st_att
                           (add (stvar v_st_att)
                                (nlit (num_of_nat 1))))
              )
              (
                nop
              )
       ]]
     | _, _ => [[ mk_vcdesc [] : nop ]]
    end.
End Spec.

Module Main := MkMain(Spec).
Import Main.