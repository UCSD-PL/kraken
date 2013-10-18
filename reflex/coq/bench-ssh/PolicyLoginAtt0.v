Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Theorem disable : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
           (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                        SLoginReq (None, (Some (num_of_nat 1), tt)))))
           (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                        SLoginReq (None, (Some (num_of_nat 1), tt)))))
          tr.
Proof.
  Time crush.
Local Transparent num_of_nat nat_of_num.
forall_not_disabler.

Qed.
