Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Tab_pat id : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Tab (Some id, (None, tt)).

Theorem enable : forall st tr id,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
    (KOExec PAYD COMPT COMPS None None (Some (Tab_pat id)))
    (KOExec PAYD COMPT COMPS None None (Some (Tab_pat id)))
    tr.
Proof.
  Time solve [crush].
Qed.
