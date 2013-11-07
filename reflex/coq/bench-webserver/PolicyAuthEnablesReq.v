Require Import Kernel PolLang ActionMatch Reflex ReflexBase ReflexFin ReflexHVec.

Import SystemFeatures.
Import Language.
Import Spec.

Theorem auth_correct : forall st tr u a,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KORecv PAYD COMPT COMPS (Some AC_pat)
      (Some (Build_opt_msg PAYD
        ACLoginResT (Some u, (Some a, tt)))))
    (KOSend PAYD COMPT COMPS (Some AC_pat)
      (Some (Build_opt_msg PAYD
        ACFileReq (Some u, (Some a, (None, tt))))))
    tr.
Proof.
  Time solve [crush].
Time Qed.

