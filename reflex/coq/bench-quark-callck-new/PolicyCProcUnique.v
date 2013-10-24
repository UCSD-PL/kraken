Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition CK_pat d : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS CProc (Some d, tt).

Theorem enable : forall st tr d,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
    (KOExec PAYD COMPT COMPS None None (Some (CK_pat d)))
    (KOExec PAYD COMPT COMPS None None (Some (CK_pat d)))
    tr.
Proof.
  Time crush.
Qed.