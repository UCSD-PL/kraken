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
  [ ("User", [str_d]) (*User name payload.*)
  ; ("AuthT", [str_d]) (*Auth response from system payload.*)
  ; ("AuthF", [])
  ].

Notation PrivReq        := 0%fin (only parsing).
Notation LoginResT      := 1%fin (only parsing).
Notation LoginResF      := 2%fin (only parsing).

(*State is (username, authres)*)
Inductive COMPT' : Type := C.
Definition COMPT := COMPT'.

Definition COMPTDEC : forall (x y : COMPT), decide (x = y).
Proof. decide equality. Defined.

Definition COMPS (t : COMPT) : compd :=
  match t with
  | C => mk_compd "Echo" "test/echo-00/test.py" [] (mk_vdesc [])
  end.

Definition KSTD : vcdesc COMPT := mk_vcdesc [Desc _ str_d; Desc _ num_d].
Definition v_user : fin (projT1 KSTD) := None.
Definition v_authed : fin (projT1 KSTD) := Some None.

Definition IENVD : vcdesc COMPT := mk_vcdesc [Comp _ C].

End SystemFeatures.

Import SystemFeatures.

Module Language := MkLanguage(SystemFeatures).

Import Language.

Definition INIT : init_prog PAYD COMPT COMPS KSTD IENVD :=
  spawn _ IENVD C tt None (Logic.eq_refl _).

Open Scope hdlr.
Definition HANDLERS : handlers PAYD COMPT COMPS KSTD :=
  fun t ct =>
  match t as _t, ct as _ct return
    {prog_envd : vcdesc COMPT & hdlr_prog PAYD COMPT COMPS KSTD _ct _t prog_envd}
  with
  | PrivReq, C =>
    [[ mk_vcdesc [] :
      ite (eq (stvar v_authed) (nlit (num_of_nat 0)))
          (
            nop
          )
          (
            send ccomp PrivReq (stvar v_user, tt)
          )
    ]]
  | LoginResT, C =>
    [[ mk_vcdesc [] :
       seq (stupd _ _ v_user   (mvar LoginResT 0%fin))
           (stupd _ _ v_authed (nlit (num_of_nat 1)))
    ]]
  | _, _ => [[ mk_vcdesc [] : nop ]]
  end.
Close Scope hdlr.
<<<<<<< Updated upstream:reflex/coq/bench-enables/Kernel.v
=======

Require Import PolLang.
Require Import ActionMatch.
Require Import List.

Local Opaque str_of_string.

Theorem enable : forall st tr u,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                         LoginResT (Some u, tt))))
          (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                         PrivReq (Some u, tt))))
          tr.
Proof.
  Time crush.
Qed.
>>>>>>> Stashed changes:reflex/coq/EnablesTest.v
