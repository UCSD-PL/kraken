Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition System_pat : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS System (None, tt).

(*The proof of the following theorem goes through. It just takes about 8gb of memory.*)
Theorem enable : forall st tr u,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
          (KORecv PAYD COMPT COMPS (Some System_pat)
                   (Some (Build_opt_msg PAYD
                                         SLoginResT (Some u, tt))))
          (KOSend PAYD COMPT COMPS None
                   (Some (Build_opt_msg PAYD
                                         SCreatePtyerReq (Some u, tt))))
          tr.
Proof.
  Time solve [crush].
Time Qed.

