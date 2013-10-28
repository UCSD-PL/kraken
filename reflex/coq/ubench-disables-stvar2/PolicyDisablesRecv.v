Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language.

Definition C_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS C tt.

Theorem disable : forall st tr,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Disables PAYD COMPT COMPS COMPTDEC
           (KORecv PAYD COMPT COMPS (Some C_pat)
                   (Some (Build_opt_msg PAYD
                                        M1 tt)))
           (KOSend PAYD COMPT COMPS (Some C_pat)
                   (Some (Build_opt_msg PAYD
                                        M2 tt)))
          tr.
Proof.
  Time solve [crush].
Qed.
