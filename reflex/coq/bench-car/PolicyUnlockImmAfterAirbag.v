Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Doors_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Doors tt.

Definition Airbag_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Airbag tt.

Theorem immafter : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
           (KOSend PAYD COMPT COMPS (Some Doors_pat)
                   (Some (Build_opt_msg PAYD
                                        UnlockDoors tt)))
           (KOSend PAYD COMPT COMPS (Some Airbag_pat)
                   (Some (Build_opt_msg PAYD
                                        InflateAirbag tt)))
          tr.
Proof.
  Time crush.
Qed.
