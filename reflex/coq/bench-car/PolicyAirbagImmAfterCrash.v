Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Engine_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Engine tt.

Definition Airbag_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Airbag tt.

(*The proof of the following theorem goes through. It just takes about 8gb of memory.*)
Theorem immafter : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
           (KOSend PAYD COMPT COMPS (Some Airbag_pat)
                   (Some (Build_opt_msg PAYD
                                        AirbagDeploy tt)))
           (KORecv PAYD COMPT COMPS (Some Engine_pat)
                   (Some (Build_opt_msg PAYD
                                        Crash tt)))
          tr.
Proof.
  Time crush.
Qed.
