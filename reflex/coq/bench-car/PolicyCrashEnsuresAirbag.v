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

Theorem ensures : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Ensures PAYD COMPT COMPS COMPTDEC
           (KORecv PAYD COMPT COMPS (Some Engine_pat)
                   (Some (Build_opt_msg PAYD
                                        Crash tt)))
           (KOSend PAYD COMPT COMPS (Some Airbag_pat)
                   (Some (Build_opt_msg PAYD
                                        InflateAirbag tt)))
          tr.
Proof.
  Time solve [crush].
Time Qed.