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
  [ ("M1", [])
  ; ("M2", [])
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
  mk_vcdesc [  Desc _ num_d
             ; Comp _ C
            ].
Notation v_st_num := 0%fin (only parsing).
Notation v_st_c   := 1%fin (only parsing).

Definition IENVD : vcdesc COMPT := mk_vcdesc [Comp _ C].
Notation v_env_c := 0%fin (only parsing).

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
   seq (spawn _ IENVD C tt v_env_c (Logic.eq_refl _))
       (stupd _ IENVD v_st_c (i_envvar IENVD v_env_c)).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | M1, C =>
    [[ mk_vcdesc [] :
       seq (send ccomp M1 tt)
           (stupd _ _ v_st_num (nlit (num_of_nat 1)))
    ]]
  | M2, C =>
    [[ mk_vcdesc [] :
       ite (eq (stvar v_st_num) (nlit (num_of_nat 1)))
           (
             nop
           )
           (
             seq (send (stvar v_st_c) M2 tt)
                 (send ccomp M2 tt)
           )
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
