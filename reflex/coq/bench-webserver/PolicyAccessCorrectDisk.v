Require Import Kernel PolLang ActionMatch Reflex ReflexBase ReflexFin ReflexHVec.

Import SystemFeatures.
Import Spec.

Theorem access_correct_disk : forall st tr u a r f,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KORecv PAYD COMPT COMPS (Some D_pat)
      (Some (Build_opt_msg PAYD
        DFileRes (Some u, (Some a, (Some r, (Some f, tt)))))))
    (KOSend PAYD COMPT COMPS (Some (Client_pat u a))
      (Some (Build_opt_msg PAYD
        FileRes (Some r, (Some f, tt)))))
    tr.
Admitted.