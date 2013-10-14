Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel Misc.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Tab_pat d : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Tab (Some d, tt).

Theorem enable : forall st tr url f,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Enables PAYD COMPT COMPS COMPTDEC
    (KOCall PAYD COMPT COMPS (Some (str_of_string (create_socket))) (Some (Some url::nil)) (Some f))
    (KOSend PAYD COMPT COMPS (Some (Tab_pat (dom url)))
      (Some (Build_opt_msg PAYD
        ResSocket (Some f, tt))))
          tr.
Proof.
  Time crush.
Qed.