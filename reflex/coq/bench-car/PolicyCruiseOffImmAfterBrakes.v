Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Brakes_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Brakes tt.

Definition CruiseCtrl_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS CruiseCtrl tt.

Theorem immafter : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmAfter PAYD COMPT COMPS COMPTDEC
           (KOSend PAYD COMPT COMPS (Some CruiseCtrl_pat)
                   (Some (Build_opt_msg PAYD
                                        CruiseOff tt)))
           (KORecv PAYD COMPT COMPS (Some Brakes_pat)
                   (Some (Build_opt_msg PAYD
                                        BrakesApplied tt)))
          tr.
Proof.
  Time crush.
Qed.