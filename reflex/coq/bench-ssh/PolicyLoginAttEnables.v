Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Theorem enable : forall st tr s,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
           (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                        SLoginReq (None, (Some s, tt)))))
           (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                        SLoginReq (None, (Some (Ascii.zero::s), tt)))))
          tr.
Proof.
  Time solve [crush].
Time Qed.

