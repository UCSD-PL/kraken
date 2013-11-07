Require Import Kernel PolLang ActionMatch Reflex ReflexBase ReflexFin ReflexHVec.

Import SystemFeatures.
Import Language.
Import Spec.

Theorem auth_correct : forall st tr u a,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
    (KOExec PAYD COMPT COMPS None None (Some (Client_pat u a)))
    (KOExec PAYD COMPT COMPS None None (Some (Client_pat u a)))
    tr.
Proof.
  Time solve [crush].
Time Qed.

