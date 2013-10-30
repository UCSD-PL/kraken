Require Import Kernel PolLang ActionMatch Reflex ReflexBase ReflexFin ReflexHVec.

Import SystemFeatures.
Import Spec.

Theorem access_correct : forall st tr u a r,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KORecv PAYD COMPT COMPS (Some AC_pat)
      (Some (Build_opt_msg PAYD
        ACFileResT (Some u, (Some a, (Some r, tt))))))
    (KOSend PAYD COMPT COMPS (Some D_pat)
      (Some (Build_opt_msg PAYD
        DFileReq (Some u, (Some a, (Some r, tt))))))
    tr.
Proof.
  Time solve [crush].
Qed.