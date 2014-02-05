Require Import String.
Require Import Reflex ReflexBase.
Require Import PolLang ActionMatch.
Require Import Kernel.

Local Opaque str_of_string.

Import SystemFeatures Language Spec.

Definition Tab_pat d : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS Tab (None, (Some d, tt)).

Definition CK_pat d : conc_pat COMPT COMPS :=
  Build_conc_pat COMPT COMPS CProc (Some d, tt).

Theorem ensures : forall st tr d f,
  Reach PAYD COMPT COMPTDEC COMPS KSTD IENVD INIT HANDLERS st ->
  ktr _ _ _ _ st = inhabits tr ->
  Ensures PAYD COMPT COMPS COMPTDEC
    (KOSend PAYD COMPT COMPS (Some (Tab_pat d))
      (Some (Build_opt_msg PAYD
        CookieProcessRegister (Some f, tt))))
    (KOSend PAYD COMPT COMPS (Some (CK_pat d))
      (Some (Build_opt_msg PAYD
        TabProcessRegister (Some f, tt))))
          tr.
Proof.
  Time solve [crush].
Time Qed.
