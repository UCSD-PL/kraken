Require Import ActionMatch Kernel PolLang Reflex.

Import SystemFeatures Language Spec.

Theorem recv_before : forall st tr m,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmBefore PAYD COMPT COMPS COMPTDEC
            (KORecv PAYD COMPT COMPS None
                     (Some (Build_opt_msg PAYD
                                          None (Some m, tt))))
            (KOSend PAYD COMPT COMPS None
                     (Some (Build_opt_msg PAYD
                                          None (Some m, tt))))
            tr.
Proof.
  Time crush.
Qed.
