Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Counter_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Counter tt.

Theorem immbefore : forall st tr u,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  ImmBefore PAYD COMPT COMPS COMPTDEC
           (KORecv PAYD COMPT COMPS (Some Counter_pat)
                   (Some (Build_opt_msg PAYD
                                        CLoginResT (Some u, tt))))
           (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                        SLoginReq (Some u, tt))))
          tr.
Proof.
  Time solve [crush].
Qed.
